//! Bridging the COS object model and `pdfcraft-crypt`: reading `/Encrypt` dictionaries and
//! decrypting / encrypting the strings and streams of an object (§7.6.2).
//!
//! Not encrypted, per the spec: the `/Encrypt` dictionary itself, cross-reference streams, the
//! trailer `/ID`, objects inside object streams (the object stream is encrypted as a whole),
//! the `/Contents` of signature dictionaries, and metadata streams when `/EncryptMetadata` is
//! false. Streams naming a crypt filter (`/Crypt` in `/Filter`) use that filter; embedded files
//! use `/EFF`.

use std::cell::Cell;

use pdfcraft_crypt::{EncryptDict, Method, SecurityHandler, StreamKind};
use pdfcraft_filters::MAX_CHAIN;

use crate::document::Held;
use crate::{Dict, Document, Object, PdfString, Stream};

std::thread_local! {
    /// Whether this thread is inside [`following`].
    static FOLLOWING: Cell<bool> = const { Cell::new(false) };
}

/// Clears [`FOLLOWING`], whatever happens while it is set.
struct Following;

impl Drop for Following {
    fn drop(&mut self) {
        FOLLOWING.set(false);
    }
}

/// What `f` gives, or `nested` if this is inside another `following`. Loading an object can read
/// what its dictionary gives by reference, and what that loads could do the same: a file could
/// make one load a tree of them, each object read again once the cache has let it go. So what is
/// loaded for this doesn't follow its own. These entries are names, arrays of them and small
/// dictionaries, which have none, so nothing a real file holds is lost.
pub(crate) fn following<T>(nested: T, f: impl FnOnce() -> T) -> T {
    if FOLLOWING.replace(true) {
        return nested;
    }
    let _following = Following;
    f()
}

/// `o`, or the object it refers to, for what decides how a stream or dictionary is treated. Inside
/// [`following`] a reference reads as absent.
fn followed<'o>(doc: &Document, o: &'o Object) -> Held<'o> {
    match o {
        Object::Ref(_) => following(Held::Direct(&Object::Null), || doc.held(o)),
        o => Held::Direct(o),
    }
}

fn bytes_of(doc: &Document, d: &Dict, key: &[u8]) -> Vec<u8> {
    d.get(key).map(|v| doc.resolve(v)).and_then(|v| v.as_string().map(|s| s.bytes.clone())).unwrap_or_default()
}

/// Read the handler parameters from an `/Encrypt` dictionary.
pub(crate) fn encrypt_dict(doc: &Document, d: &Dict) -> EncryptDict {
    let int = |k: &[u8], default: i64| d.get(k).map(|v| doc.resolve(v)).and_then(|v| v.as_int()).unwrap_or(default);
    let name = |d: &Dict, k: &[u8]| d.get(k).and_then(|v| doc.resolve(v).as_name().map(<[u8]>::to_vec));
    let mut crypt_filters = Vec::new();
    if let Some(cf) = d.get(b"CF").map(|c| doc.resolve(c)).and_then(|c| c.as_dict().cloned()) {
        for (k, v) in cf.iter() {
            let Some(f) = doc.resolve(v).as_dict().cloned() else { continue };
            let method = match name(&f, b"CFM").as_deref() {
                Some(b"V2") => Method::Rc4,
                Some(b"AESV2") => Method::Aes128,
                Some(b"AESV3") => Method::Aes256,
                _ => Method::Identity,
            };
            crypt_filters.push((k.clone(), method));
        }
    }
    let v = int(b"V", 0);
    // V4: the key length comes from the standard crypt filter's /Length (bytes, or bits in
    // some files); /Length on the dictionary is often a stale 40. A length that isn't
    // positive means nothing and reads as if absent.
    let cf_len = d
        .get(b"CF")
        .map(|c| doc.resolve(c))
        .and_then(|c| c.as_dict().and_then(|c| c.get(b"StdCF").map(|f| doc.resolve(f))))
        .and_then(|f| f.as_dict().and_then(|f| f.get(b"Length").map(|n| doc.resolve(n))))
        .and_then(|n| n.as_int())
        .filter(|n| *n > 0);
    let length_bits = match (v, cf_len) {
        (5.., _) => 256,
        (4, Some(n)) if n <= 32 => n * 8,
        (4, Some(n)) => n,
        (4, None) => 128,
        _ => int(b"Length", 40),
    };
    EncryptDict {
        filter: name(d, b"Filter").unwrap_or_default(),
        v,
        r: int(b"R", 0),
        length_bits,
        o: bytes_of(doc, d, b"O"),
        u: bytes_of(doc, d, b"U"),
        oe: bytes_of(doc, d, b"OE"),
        ue: bytes_of(doc, d, b"UE"),
        perms: bytes_of(doc, d, b"Perms"),
        p: int(b"P", -1) as i32,
        encrypt_metadata: !matches!(d.get(b"EncryptMetadata").map(|v| doc.resolve(v)).as_deref(), Some(Object::Bool(false))),
        crypt_filters,
        stm_f: name(d, b"StmF").unwrap_or_else(|| b"Identity".to_vec()),
        str_f: name(d, b"StrF").unwrap_or_else(|| b"Identity".to_vec()),
        ef_f: name(d, b"EFF").unwrap_or_default(),
    }
}

/// Whether `f`, an entry of a `/Filter` chain or its only filter, is `/Crypt`.
fn is_crypt(doc: &Document, f: &Object) -> bool {
    followed(doc, f).as_name() == Some(b"Crypt")
}

/// The crypt filter a stream names in its `/Filter` chain (`/Crypt` + `/DecodeParms /Name`), each
/// given directly or by reference, in an array or not. A chain longer than any decoder takes names
/// none: nothing can read that stream anyway, and every stream of a file can share one long array.
fn named_crypt_filter(doc: &Document, dict: &Dict) -> Option<Vec<u8>> {
    let filter = followed(doc, dict.get(b"Filter")?);
    let i = match &*filter {
        Object::Array(a) if a.len() <= MAX_CHAIN + 1 => a.iter().position(|f| is_crypt(doc, f))?,
        f if is_crypt(doc, f) => 0,
        _ => return None,
    };
    let parms = dict.get(b"DecodeParms").map(|p| followed(doc, p));
    let entry = match parms.as_deref() {
        Some(Object::Array(a)) => a.get(i).map(|p| followed(doc, p)),
        Some(p) if i == 0 => Some(Held::Direct(p)),
        _ => None,
    };
    let name = entry.as_deref().and_then(Object::as_dict).and_then(|p| p.get(b"Name")).map(|n| followed(doc, n));
    Some(name.as_deref().and_then(Object::as_name).map_or_else(|| b"Identity".to_vec(), <[u8]>::to_vec))
}

/// A signature dictionary (field signature, document timestamp or usage-rights signature),
/// whose `/Contents` is never encrypted (ISO 32000-2 §7.6.2, §12.8.1): the signer writes a
/// placeholder, hashes the file around it and patches the value in place, so encrypting it
/// would make signing impossible. Identified as other readers do: by `/Type`, or by a string
/// `/Contents` alongside an array `/ByteRange` (`/Type` is optional). A signature dictionary
/// has no `/Subtype`; a dictionary with one (an annotation, whose `/Contents` is the comment
/// text) or with another `/Type` is never exempt, whatever else it carries.
fn is_signature_dict(doc: &Document, d: &Dict) -> bool {
    // A null entry, or one that refers to nothing, is an absent one (ISO 32000-2 §7.3.7, §7.3.10).
    let entry = |key: &[u8]| d.get(key).map(|v| followed(doc, v)).filter(|v| !matches!(**v, Object::Null));
    if entry(b"Subtype").is_some() {
        return false;
    }
    match entry(b"Type") {
        Some(t) => matches!(t.as_name(), Some(b"Sig" | b"DocTimeStamp")),
        None => matches!(d.get(b"Contents"), Some(Object::String(_))) && matches!(entry(b"ByteRange").as_deref(), Some(Object::Array(_))),
    }
}

/// `source` without the `/Crypt` entries of its filter chain and their decode parameters, the two
/// made direct if they were given by reference. Called on a dictionary [`named_crypt_filter`] found
/// a filter in, so the chain is short, and no more parameters are copied than it has filters.
fn drop_crypt_filter(doc: &Document, source: &Dict) -> Dict {
    let mut dict = source.clone();
    let filter = source.get(b"Filter").map(|f| followed(doc, f));
    let chain = match filter.as_deref() {
        Some(Object::Array(a)) => a.clone(),
        Some(f) => vec![f.clone()],
        None => Vec::new(),
    };
    let crypt: Vec<bool> = chain.iter().map(|f| is_crypt(doc, f)).collect();
    // A lone parameter dictionary belongs to the first filter (as `named_crypt_filter` reads it).
    match source.get(b"DecodeParms").map(|p| followed(doc, p)).as_deref() {
        Some(Object::Array(p)) => {
            let parms: Vec<Object> = p.iter().zip(&crypt).filter(|(_, c)| !**c).map(|(p, _)| p.clone()).collect();
            dict.set(b"DecodeParms".to_vec(), Object::Array(parms));
        }
        Some(Object::Dict(_)) if crypt.first() == Some(&true) => {
            dict.remove(b"DecodeParms");
        }
        _ => {}
    }
    let filters: Vec<Object> = chain.into_iter().zip(&crypt).filter(|(_, c)| !**c).map(|(f, _)| f).collect();
    if filters.is_empty() {
        dict.remove(b"Filter");
        if matches!(dict.get(b"DecodeParms"), Some(Object::Array(p)) if p.is_empty()) {
            dict.remove(b"DecodeParms");
        }
    } else {
        dict.set(b"Filter".to_vec(), Object::Array(filters));
    }
    dict
}

/// What [`transform`] does to an object.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Pass {
    /// Decrypt, with the handler the document was opened with.
    Decrypt,
    /// Encrypt with the handler the document was opened with: streams keep their crypt filters.
    Encrypt,
    /// Encrypt with protection applied by `set_encryption`. A stream's crypt filter came from
    /// the source's `/Encrypt`; unless the new one defines that name it is dropped, so the
    /// stream follows the new policy instead of reading as `/Identity` and staying in clear.
    EncryptReplacing,
}

/// Decrypt or encrypt every string and stream in an indirect object, except a signature
/// dictionary's `/Contents` (see [`is_signature_dict`]).
///
/// `o` is as `doc` holds it: what a stream's dictionary gives by reference is read from `doc`, so
/// its references have to be the document's, not a save's renumbered ones.
pub(crate) fn transform(doc: &Document, h: &SecurityHandler, o: &Object, num: u32, generation: u16, pass: Pass) -> Object {
    let decrypt = pass == Pass::Decrypt;
    let strings = |s: &PdfString| {
        let bytes = if decrypt { h.decrypt_string(num, generation, &s.bytes) } else { h.encrypt_string(num, generation, &s.bytes) };
        PdfString { bytes, hex: s.hex || !decrypt }
    };
    walk(doc, o, &strings, h, num, generation, pass)
}

fn walk(doc: &Document, o: &Object, strings: &dyn Fn(&PdfString) -> PdfString, h: &SecurityHandler, num: u32, generation: u16, pass: Pass) -> Object {
    let decrypt = pass == Pass::Decrypt;
    match o {
        Object::String(s) => Object::String(strings(s)),
        Object::Array(a) => Object::Array(a.iter().map(|x| walk(doc, x, strings, h, num, generation, pass)).collect()),
        Object::Dict(d) if is_signature_dict(doc, d) => Object::Dict(
            d.iter()
                .map(|(k, v)| match (k.as_slice(), v) {
                    (b"Contents", Object::String(_)) => (k.clone(), v.clone()),
                    _ => (k.clone(), walk(doc, v, strings, h, num, generation, pass)),
                })
                .collect(),
        ),
        Object::Dict(d) => Object::Dict(d.iter().map(|(k, v)| (k.clone(), walk(doc, v, strings, h, num, generation, pass))).collect()),
        Object::Stream(s) => {
            let walked = |d: &Dict| -> Dict { d.iter().map(|(k, v)| (k.clone(), walk(doc, v, strings, h, num, generation, pass))).collect() };
            let ty = s.dict.get(b"Type").map(|t| followed(doc, t));
            let ty = ty.as_deref().and_then(Object::as_name);
            // Cross-reference streams are never encrypted (§7.5.8), but only reading may trust the
            // label: a stream a producer calls /XRef stays plaintext if writing believes it, and the
            // writer builds its own cross-reference streams outside this transform.
            if (decrypt && ty == Some(b"XRef")) || (ty == Some(b"Metadata") && !h.encrypts_metadata()) {
                return Object::Stream(Stream { dict: walked(&s.dict), raw: s.raw.clone() });
            }
            let mut named = named_crypt_filter(doc, &s.dict);
            // Before the walk: what it copies out of a reference has strings to encrypt as well.
            let foreign = pass == Pass::EncryptReplacing && named.as_deref().is_some_and(|n| !h.dict().crypt_filters.iter().any(|(f, _)| f == n));
            let dropped = foreign.then(|| drop_crypt_filter(doc, &s.dict));
            if dropped.is_some() {
                named = None;
            }
            let dict = walked(dropped.as_ref().unwrap_or(&s.dict));
            let kind = match (&named, ty) {
                (Some(n), _) => StreamKind::Named(n),
                (None, Some(b"EmbeddedFile")) => StreamKind::EmbeddedFile,
                _ => StreamKind::Normal,
            };
            let raw = if decrypt { h.decrypt_stream(num, generation, &s.raw, kind) } else { h.encrypt_stream(num, generation, &s.raw, kind) };
            Object::Stream(Stream { dict, raw: raw.into() })
        }
        other => other.clone(),
    }
}
