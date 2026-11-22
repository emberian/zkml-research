//! Toolkit-free 25-variant `ViewNode` IR, canonical binary codec, deterministic tree diff/patch,
//! `Frustum` fog-of-war observer scrubber, and constructive `synthesize_repair_badge`.
//!
//! Quarried cleanly from `breadstuffs/deos-view/src/{tree.rs,fmt.rs}` and
//! `obend/lean/Obend/Vault/{FrustumMembrane.lean,Affordance.lean}` with zero GPUI and zero
//! legacy `cell` dependencies.

use std::collections::{BTreeMap, BTreeSet};

/// Maximum nesting depth permitted by the canonical codec (matches `deos-view/src/tree.rs:1103`).
pub const MAX_VIEW_DEPTH: usize = 16;
/// Maximum total nodes permitted by the canonical codec (matches `deos-view/src/tree.rs:1105`).
pub const MAX_VIEW_NODES: usize = 4096;
/// Canonical binary wire magic (`deos-view` `ViewNode` v1).
pub const VIEWNODE_WIRE_MAGIC: &[u8; 4] = b"DVN1";
pub const VIEWNODE_WIRE_VERSION: u8 = 1;

/// Display formatting for `ViewNode::Bind` (`deos-view/src/fmt.rs:24`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum BindFmt {
    #[default]
    Raw,
    Hex,
    Id,
    Amount,
}

impl BindFmt {
    pub fn from_prop(s: Option<&str>) -> Self {
        match s.unwrap_or("") {
            "id" | "key" => BindFmt::Id,
            "hash" | "hex" => BindFmt::Hex,
            "amount" => BindFmt::Amount,
            _ => BindFmt::Raw,
        }
    }

    pub fn as_str(self) -> &'static str {
        match self {
            BindFmt::Raw => "raw",
            BindFmt::Hex => "hex",
            BindFmt::Id => "id",
            BindFmt::Amount => "amount",
        }
    }

    fn to_tag(self) -> u8 {
        match self {
            BindFmt::Raw => 0,
            BindFmt::Hex => 1,
            BindFmt::Id => 2,
            BindFmt::Amount => 3,
        }
    }

    fn from_tag(b: u8) -> Result<Self, CodecError> {
        match b {
            0 => Ok(BindFmt::Raw),
            1 => Ok(BindFmt::Hex),
            2 => Ok(BindFmt::Id),
            3 => Ok(BindFmt::Amount),
            other => Err(CodecError::InvalidTag("BindFmt", other)),
        }
    }
}

const AVATAR_EMOJI: [&str; 16] = [
    "🦊", "🐢", "🦉", "🐙", "🦋", "🐝", "🐬", "🦁", "🐼", "🦅", "🦄", "🐳", "🦖", "🦜", "🦦", "🦩",
];
const AVATAR_ADJ: [&str; 16] = [
    "swift", "brave", "calm", "bright", "lucky", "noble", "quiet", "merry", "bold", "gentle",
    "clever", "sunny", "cozy", "keen", "jolly", "wise",
];
const AVATAR_NOUN: [&str; 16] = [
    "fox", "owl", "wren", "lynx", "moth", "hare", "finch", "otter", "crane", "vole", "newt", "koi",
    "dove", "elk", "mole", "swan",
];

fn splitmix64(mut z: u64) -> u64 {
    z = z.wrapping_add(0x9e37_79b9_7f4a_7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

/// Renderer-independent bound value formatter (`deos-view/src/fmt.rs:63`).
pub fn format_value(value: u64, fmt: BindFmt) -> String {
    match fmt {
        BindFmt::Raw => value.to_string(),
        BindFmt::Hex => {
            let h = format!("{value:x}");
            if h.len() > 8 {
                format!("0x{}…{}", &h[..4], &h[h.len() - 4..])
            } else {
                format!("0x{h}")
            }
        }
        BindFmt::Id => {
            let m = splitmix64(value);
            let e = AVATAR_EMOJI[(m & 0xf) as usize];
            let a = AVATAR_ADJ[((m >> 8) & 0xf) as usize];
            let n = AVATAR_NOUN[((m >> 16) & 0xf) as usize];
            format!("{e} {a}-{n}")
        }
        BindFmt::Amount => {
            let s = value.to_string();
            let bytes = s.as_bytes();
            let len = bytes.len();
            let mut out = String::with_capacity(len + len / 3);
            for (i, b) in bytes.iter().enumerate() {
                if i > 0 && (len - i).is_multiple_of(3) {
                    out.push(',');
                }
                out.push(*b as char);
            }
            out
        }
    }
}

/// Progressive disclosure level (`deos-view/src/tree.rs:267`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum Disclosure {
    #[default]
    Simple,
    Adept,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PillCase {
    pub value: u64,
    pub label: String,
    pub tag: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Crumb {
    pub label: String,
    pub turn: String,
    pub arg: i64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MenuItem {
    pub label: String,
    pub turn: String,
    pub arg: i64,
    pub enabled: bool,
    pub wants_text: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HaloHandle {
    pub glyph: String,
    pub turn: String,
    pub arg: i64,
    pub enabled: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoordCell {
    pub glyph: String,
    pub tag: String,
    pub turn: String,
    pub arg: i64,
    pub highlight: bool,
}

/// Projection status attached to a `ViewNode::Host` boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HostStatus {
    Live,
    Severed { snapshot_digest: u64 },
    Attenuated { allowed_count: usize },
    Interposed { mock_label: String },
}

/// Complete 25-variant toolkit-free `ViewNode` IR matching `breadstuffs/deos-view/src/tree.rs:25-249`
/// and `Minidregg.Assurance.LightClientAndViewLens.ViewNode`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ViewNode {
    // 1..8: core layout & interactive nodes
    VStack(Vec<ViewNode>),
    Row(Vec<ViewNode>),
    Text(String),
    Bind {
        slot: usize,
        label: String,
        fmt: BindFmt,
        resolved: Option<u64>,
    },
    Button {
        label: String,
        turn: String,
        arg: i64,
    },
    Input {
        bind_view: String,
        fire_turn: String,
        submit_label: String,
    },
    List(Vec<ViewNode>),
    Table(Vec<ViewNode>),
    // 9..12: richness expansion batch 1
    Section {
        title: String,
        tag: String,
        children: Vec<ViewNode>,
    },
    Tabs {
        tabs: Vec<String>,
        selected_slot: usize,
        select_turn: String,
        resolved_active: Option<u64>,
        panels: Vec<ViewNode>,
    },
    Gauge {
        slot: usize,
        max: u64,
        label: String,
        resolved: Option<u64>,
    },
    Divider,
    // 13: fractal cell-hosted composition keystone
    Host {
        cell: String,
        status: HostStatus,
        view: Option<Box<ViewNode>>,
    },
    // 14..24: richness expansion batch 2
    Grid {
        cols: usize,
        children: Vec<ViewNode>,
    },
    Breadcrumb {
        items: Vec<Crumb>,
    },
    Progress {
        value: u64,
        max: u64,
        label: String,
    },
    Pill {
        text: String,
        tag: String,
        slot: Option<usize>,
        cases: Vec<PillCase>,
        resolved: Option<u64>,
    },
    Icon {
        glyph: String,
        tag: String,
    },
    Menu {
        items: Vec<MenuItem>,
    },
    Halo {
        target_slot: usize,
        handles: Vec<HaloHandle>,
    },
    Slider {
        slot: usize,
        min: u64,
        max: u64,
        turn: String,
        resolved: Option<u64>,
    },
    Toggle {
        slot: usize,
        on_turn: String,
        off_turn: String,
        glyph_on: String,
        glyph_off: String,
        label: String,
        resolved: Option<u64>,
    },
    Tile {
        handle: String,
        w: u32,
        h: u32,
    },
    CoordGrid {
        cols: usize,
        cells: Vec<CoordCell>,
    },
    // 25: progressive disclosure wrapper
    Adept(Box<ViewNode>),
}

impl ViewNode {
    /// Stable canonical discriminant tag `0..=24` for the 25 variants.
    pub fn variant_tag(&self) -> u8 {
        match self {
            ViewNode::VStack(_) => 0,
            ViewNode::Row(_) => 1,
            ViewNode::Text(_) => 2,
            ViewNode::Bind { .. } => 3,
            ViewNode::Button { .. } => 4,
            ViewNode::Input { .. } => 5,
            ViewNode::List(_) => 6,
            ViewNode::Table(_) => 7,
            ViewNode::Section { .. } => 8,
            ViewNode::Tabs { .. } => 9,
            ViewNode::Gauge { .. } => 10,
            ViewNode::Divider => 11,
            ViewNode::Host { .. } => 12,
            ViewNode::Grid { .. } => 13,
            ViewNode::Breadcrumb { .. } => 14,
            ViewNode::Progress { .. } => 15,
            ViewNode::Pill { .. } => 16,
            ViewNode::Icon { .. } => 17,
            ViewNode::Menu { .. } => 18,
            ViewNode::Halo { .. } => 19,
            ViewNode::Slider { .. } => 20,
            ViewNode::Toggle { .. } => 21,
            ViewNode::Tile { .. } => 22,
            ViewNode::CoordGrid { .. } => 23,
            ViewNode::Adept(_) => 24,
        }
    }

    /// Encode this `ViewNode` into canonical deterministic binary form (`DVN1`).
    pub fn encode(&self) -> Result<Vec<u8>, CodecError> {
        let mut buf = Vec::new();
        buf.extend_from_slice(VIEWNODE_WIRE_MAGIC);
        buf.push(VIEWNODE_WIRE_VERSION);
        let mut node_count = 0usize;
        encode_node(self, 0, &mut node_count, &mut buf)?;
        Ok(buf)
    }

    /// Decode a canonical `DVN1` binary `ViewNode`, enforcing depth, node-count, UTF-8,
    /// and trailing-byte invariants.
    pub fn decode(bytes: &[u8]) -> Result<Self, CodecError> {
        if bytes.len() < 5 {
            return Err(CodecError::UnexpectedEof);
        }
        if &bytes[0..4] != VIEWNODE_WIRE_MAGIC {
            return Err(CodecError::BadMagic);
        }
        if bytes[4] != VIEWNODE_WIRE_VERSION {
            return Err(CodecError::UnsupportedVersion(bytes[4]));
        }
        let mut r = Reader {
            bytes: &bytes[5..],
            pos: 0,
            node_count: 0,
        };
        let node = decode_node(&mut r, 0)?;
        if r.pos != r.bytes.len() {
            return Err(CodecError::TrailingBytes(r.bytes.len() - r.pos));
        }
        Ok(node)
    }
}

/// Apply progressive disclosure (`deos-view/src/tree.rs:293`).
pub fn disclose(tree: &ViewNode, level: Disclosure) -> ViewNode {
    fn rec(node: &ViewNode, level: Disclosure) -> Option<ViewNode> {
        match node {
            ViewNode::Adept(inner) => match level {
                Disclosure::Simple => None,
                Disclosure::Adept => rec(inner, level),
            },
            ViewNode::VStack(cs) => Some(ViewNode::VStack(kids(cs, level))),
            ViewNode::Row(cs) => Some(ViewNode::Row(kids(cs, level))),
            ViewNode::List(cs) => Some(ViewNode::List(kids(cs, level))),
            ViewNode::Table(cs) => Some(ViewNode::Table(kids(cs, level))),
            ViewNode::Section {
                title,
                tag,
                children,
            } => Some(ViewNode::Section {
                title: title.clone(),
                tag: tag.clone(),
                children: kids(children, level),
            }),
            ViewNode::Tabs {
                tabs,
                selected_slot,
                select_turn,
                resolved_active,
                panels,
            } => Some(ViewNode::Tabs {
                tabs: tabs.clone(),
                selected_slot: *selected_slot,
                select_turn: select_turn.clone(),
                resolved_active: *resolved_active,
                panels: kids(panels, level),
            }),
            ViewNode::Grid { cols, children } => Some(ViewNode::Grid {
                cols: *cols,
                children: kids(children, level),
            }),
            ViewNode::Host { cell, status, view } => Some(ViewNode::Host {
                cell: cell.clone(),
                status: status.clone(),
                view: view.as_ref().and_then(|v| rec(v, level)).map(Box::new),
            }),
            leaf => Some(leaf.clone()),
        }
    }
    fn kids(children: &[ViewNode], level: Disclosure) -> Vec<ViewNode> {
        children.iter().filter_map(|c| rec(c, level)).collect()
    }
    rec(tree, level).unwrap_or_else(|| ViewNode::VStack(Vec::new()))
}

// ---------------------------------------------------------------------------
// Canonical Binary Codec
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CodecError {
    BadMagic,
    UnsupportedVersion(u8),
    UnexpectedEof,
    InvalidTag(&'static str, u8),
    InvalidBool(u8),
    InvalidUtf8,
    DepthExceeded(usize),
    NodeBudgetExceeded(usize),
    TrailingBytes(usize),
    LengthOverflow,
}

fn put_u32(buf: &mut Vec<u8>, v: u32) {
    buf.extend_from_slice(&v.to_le_bytes());
}

fn put_u64(buf: &mut Vec<u8>, v: u64) {
    buf.extend_from_slice(&v.to_le_bytes());
}

fn put_i64(buf: &mut Vec<u8>, v: i64) {
    buf.extend_from_slice(&v.to_le_bytes());
}

fn put_usize(buf: &mut Vec<u8>, v: usize) -> Result<(), CodecError> {
    let u = u32::try_from(v).map_err(|_| CodecError::LengthOverflow)?;
    put_u32(buf, u);
    Ok(())
}

fn put_str(buf: &mut Vec<u8>, s: &str) -> Result<(), CodecError> {
    put_usize(buf, s.len())?;
    buf.extend_from_slice(s.as_bytes());
    Ok(())
}

fn put_opt_u64(buf: &mut Vec<u8>, opt: Option<u64>) {
    match opt {
        None => buf.push(0),
        Some(v) => {
            buf.push(1);
            put_u64(buf, v);
        }
    }
}

fn put_opt_usize(buf: &mut Vec<u8>, opt: Option<usize>) -> Result<(), CodecError> {
    match opt {
        None => {
            buf.push(0);
            Ok(())
        }
        Some(v) => {
            buf.push(1);
            put_usize(buf, v)
        }
    }
}

fn encode_children(
    cs: &[ViewNode],
    depth: usize,
    node_count: &mut usize,
    buf: &mut Vec<u8>,
) -> Result<(), CodecError> {
    put_usize(buf, cs.len())?;
    for c in cs {
        encode_node(c, depth + 1, node_count, buf)?;
    }
    Ok(())
}

fn encode_node(
    node: &ViewNode,
    depth: usize,
    node_count: &mut usize,
    buf: &mut Vec<u8>,
) -> Result<(), CodecError> {
    if depth > MAX_VIEW_DEPTH {
        return Err(CodecError::DepthExceeded(depth));
    }
    *node_count += 1;
    if *node_count > MAX_VIEW_NODES {
        return Err(CodecError::NodeBudgetExceeded(*node_count));
    }
    buf.push(node.variant_tag());
    match node {
        ViewNode::VStack(cs) | ViewNode::Row(cs) | ViewNode::List(cs) | ViewNode::Table(cs) => {
            encode_children(cs, depth, node_count, buf)?;
        }
        ViewNode::Text(s) => put_str(buf, s)?,
        ViewNode::Bind {
            slot,
            label,
            fmt,
            resolved,
        } => {
            put_usize(buf, *slot)?;
            put_str(buf, label)?;
            buf.push(fmt.to_tag());
            put_opt_u64(buf, *resolved);
        }
        ViewNode::Button { label, turn, arg } => {
            put_str(buf, label)?;
            put_str(buf, turn)?;
            put_i64(buf, *arg);
        }
        ViewNode::Input {
            bind_view,
            fire_turn,
            submit_label,
        } => {
            put_str(buf, bind_view)?;
            put_str(buf, fire_turn)?;
            put_str(buf, submit_label)?;
        }
        ViewNode::Section {
            title,
            tag,
            children,
        } => {
            put_str(buf, title)?;
            put_str(buf, tag)?;
            encode_children(children, depth, node_count, buf)?;
        }
        ViewNode::Tabs {
            tabs,
            selected_slot,
            select_turn,
            resolved_active,
            panels,
        } => {
            put_usize(buf, tabs.len())?;
            for t in tabs {
                put_str(buf, t)?;
            }
            put_usize(buf, *selected_slot)?;
            put_str(buf, select_turn)?;
            put_opt_u64(buf, *resolved_active);
            encode_children(panels, depth, node_count, buf)?;
        }
        ViewNode::Gauge {
            slot,
            max,
            label,
            resolved,
        } => {
            put_usize(buf, *slot)?;
            put_u64(buf, *max);
            put_str(buf, label)?;
            put_opt_u64(buf, *resolved);
        }
        ViewNode::Divider => {}
        ViewNode::Host { cell, status, view } => {
            put_str(buf, cell)?;
            match status {
                HostStatus::Live => buf.push(0),
                HostStatus::Severed { snapshot_digest } => {
                    buf.push(1);
                    put_u64(buf, *snapshot_digest);
                }
                HostStatus::Attenuated { allowed_count } => {
                    buf.push(2);
                    put_usize(buf, *allowed_count)?;
                }
                HostStatus::Interposed { mock_label } => {
                    buf.push(3);
                    put_str(buf, mock_label)?;
                }
            }
            match view {
                None => buf.push(0),
                Some(inner) => {
                    buf.push(1);
                    encode_node(inner, depth + 1, node_count, buf)?;
                }
            }
        }
        ViewNode::Grid { cols, children } => {
            put_usize(buf, *cols)?;
            encode_children(children, depth, node_count, buf)?;
        }
        ViewNode::Breadcrumb { items } => {
            put_usize(buf, items.len())?;
            for c in items {
                put_str(buf, &c.label)?;
                put_str(buf, &c.turn)?;
                put_i64(buf, c.arg);
            }
        }
        ViewNode::Progress { value, max, label } => {
            put_u64(buf, *value);
            put_u64(buf, *max);
            put_str(buf, label)?;
        }
        ViewNode::Pill {
            text,
            tag,
            slot,
            cases,
            resolved,
        } => {
            put_str(buf, text)?;
            put_str(buf, tag)?;
            put_opt_usize(buf, *slot)?;
            put_usize(buf, cases.len())?;
            for pc in cases {
                put_u64(buf, pc.value);
                put_str(buf, &pc.label)?;
                put_str(buf, &pc.tag)?;
            }
            put_opt_u64(buf, *resolved);
        }
        ViewNode::Icon { glyph, tag } => {
            put_str(buf, glyph)?;
            put_str(buf, tag)?;
        }
        ViewNode::Menu { items } => {
            put_usize(buf, items.len())?;
            for it in items {
                put_str(buf, &it.label)?;
                put_str(buf, &it.turn)?;
                put_i64(buf, it.arg);
                buf.push(u8::from(it.enabled));
                buf.push(u8::from(it.wants_text));
            }
        }
        ViewNode::Halo {
            target_slot,
            handles,
        } => {
            put_usize(buf, *target_slot)?;
            put_usize(buf, handles.len())?;
            for h in handles {
                put_str(buf, &h.glyph)?;
                put_str(buf, &h.turn)?;
                put_i64(buf, h.arg);
                buf.push(u8::from(h.enabled));
            }
        }
        ViewNode::Slider {
            slot,
            min,
            max,
            turn,
            resolved,
        } => {
            put_usize(buf, *slot)?;
            put_u64(buf, *min);
            put_u64(buf, *max);
            put_str(buf, turn)?;
            put_opt_u64(buf, *resolved);
        }
        ViewNode::Toggle {
            slot,
            on_turn,
            off_turn,
            glyph_on,
            glyph_off,
            label,
            resolved,
        } => {
            put_usize(buf, *slot)?;
            put_str(buf, on_turn)?;
            put_str(buf, off_turn)?;
            put_str(buf, glyph_on)?;
            put_str(buf, glyph_off)?;
            put_str(buf, label)?;
            put_opt_u64(buf, *resolved);
        }
        ViewNode::Tile { handle, w, h } => {
            put_str(buf, handle)?;
            put_u32(buf, *w);
            put_u32(buf, *h);
        }
        ViewNode::CoordGrid { cols, cells } => {
            put_usize(buf, *cols)?;
            put_usize(buf, cells.len())?;
            for cell in cells {
                put_str(buf, &cell.glyph)?;
                put_str(buf, &cell.tag)?;
                put_str(buf, &cell.turn)?;
                put_i64(buf, cell.arg);
                buf.push(u8::from(cell.highlight));
            }
        }
        ViewNode::Adept(inner) => encode_node(inner, depth + 1, node_count, buf)?,
    }
    Ok(())
}

struct Reader<'a> {
    bytes: &'a [u8],
    pos: usize,
    node_count: usize,
}

impl<'a> Reader<'a> {
    fn read_exact(&mut self, n: usize) -> Result<&'a [u8], CodecError> {
        let end = self.pos.checked_add(n).ok_or(CodecError::UnexpectedEof)?;
        if end > self.bytes.len() {
            return Err(CodecError::UnexpectedEof);
        }
        let slice = &self.bytes[self.pos..end];
        self.pos = end;
        Ok(slice)
    }

    fn read_u8(&mut self) -> Result<u8, CodecError> {
        Ok(self.read_exact(1)?[0])
    }

    fn read_bool(&mut self) -> Result<bool, CodecError> {
        match self.read_u8()? {
            0 => Ok(false),
            1 => Ok(true),
            other => Err(CodecError::InvalidBool(other)),
        }
    }

    fn read_u32(&mut self) -> Result<u32, CodecError> {
        let mut b = [0u8; 4];
        b.copy_from_slice(self.read_exact(4)?);
        Ok(u32::from_le_bytes(b))
    }

    fn read_usize(&mut self) -> Result<usize, CodecError> {
        Ok(self.read_u32()? as usize)
    }

    fn read_u64(&mut self) -> Result<u64, CodecError> {
        let mut b = [0u8; 8];
        b.copy_from_slice(self.read_exact(8)?);
        Ok(u64::from_le_bytes(b))
    }

    fn read_i64(&mut self) -> Result<i64, CodecError> {
        let mut b = [0u8; 8];
        b.copy_from_slice(self.read_exact(8)?);
        Ok(i64::from_le_bytes(b))
    }

    fn read_str(&mut self) -> Result<String, CodecError> {
        let len = self.read_usize()?;
        let slice = self.read_exact(len)?;
        std::str::from_utf8(slice)
            .map(|s| s.to_owned())
            .map_err(|_| CodecError::InvalidUtf8)
    }

    fn read_opt_u64(&mut self) -> Result<Option<u64>, CodecError> {
        match self.read_u8()? {
            0 => Ok(None),
            1 => Ok(Some(self.read_u64()?)),
            other => Err(CodecError::InvalidTag("Option<u64>", other)),
        }
    }

    fn read_opt_usize(&mut self) -> Result<Option<usize>, CodecError> {
        match self.read_u8()? {
            0 => Ok(None),
            1 => Ok(Some(self.read_usize()?)),
            other => Err(CodecError::InvalidTag("Option<usize>", other)),
        }
    }
}

fn decode_children(r: &mut Reader<'_>, depth: usize) -> Result<Vec<ViewNode>, CodecError> {
    let n = r.read_usize()?;
    if n > MAX_VIEW_NODES {
        return Err(CodecError::NodeBudgetExceeded(n));
    }
    let mut out = Vec::with_capacity(n);
    for _ in 0..n {
        out.push(decode_node(r, depth + 1)?);
    }
    Ok(out)
}

fn decode_node(r: &mut Reader<'_>, depth: usize) -> Result<ViewNode, CodecError> {
    if depth > MAX_VIEW_DEPTH {
        return Err(CodecError::DepthExceeded(depth));
    }
    r.node_count += 1;
    if r.node_count > MAX_VIEW_NODES {
        return Err(CodecError::NodeBudgetExceeded(r.node_count));
    }
    let tag = r.read_u8()?;
    match tag {
        0 => Ok(ViewNode::VStack(decode_children(r, depth)?)),
        1 => Ok(ViewNode::Row(decode_children(r, depth)?)),
        2 => Ok(ViewNode::Text(r.read_str()?)),
        3 => Ok(ViewNode::Bind {
            slot: r.read_usize()?,
            label: r.read_str()?,
            fmt: BindFmt::from_tag(r.read_u8()?)?,
            resolved: r.read_opt_u64()?,
        }),
        4 => Ok(ViewNode::Button {
            label: r.read_str()?,
            turn: r.read_str()?,
            arg: r.read_i64()?,
        }),
        5 => Ok(ViewNode::Input {
            bind_view: r.read_str()?,
            fire_turn: r.read_str()?,
            submit_label: r.read_str()?,
        }),
        6 => Ok(ViewNode::List(decode_children(r, depth)?)),
        7 => Ok(ViewNode::Table(decode_children(r, depth)?)),
        8 => Ok(ViewNode::Section {
            title: r.read_str()?,
            tag: r.read_str()?,
            children: decode_children(r, depth)?,
        }),
        9 => {
            let tn = r.read_usize()?;
            if tn > MAX_VIEW_NODES {
                return Err(CodecError::NodeBudgetExceeded(tn));
            }
            let mut tabs = Vec::with_capacity(tn);
            for _ in 0..tn {
                tabs.push(r.read_str()?);
            }
            Ok(ViewNode::Tabs {
                tabs,
                selected_slot: r.read_usize()?,
                select_turn: r.read_str()?,
                resolved_active: r.read_opt_u64()?,
                panels: decode_children(r, depth)?,
            })
        }
        10 => Ok(ViewNode::Gauge {
            slot: r.read_usize()?,
            max: r.read_u64()?,
            label: r.read_str()?,
            resolved: r.read_opt_u64()?,
        }),
        11 => Ok(ViewNode::Divider),
        12 => {
            let cell = r.read_str()?;
            let status = match r.read_u8()? {
                0 => HostStatus::Live,
                1 => HostStatus::Severed {
                    snapshot_digest: r.read_u64()?,
                },
                2 => HostStatus::Attenuated {
                    allowed_count: r.read_usize()?,
                },
                3 => HostStatus::Interposed {
                    mock_label: r.read_str()?,
                },
                other => return Err(CodecError::InvalidTag("HostStatus", other)),
            };
            let view = match r.read_u8()? {
                0 => None,
                1 => Some(Box::new(decode_node(r, depth + 1)?)),
                other => return Err(CodecError::InvalidTag("Host.view", other)),
            };
            Ok(ViewNode::Host { cell, status, view })
        }
        13 => Ok(ViewNode::Grid {
            cols: r.read_usize()?,
            children: decode_children(r, depth)?,
        }),
        14 => {
            let n = r.read_usize()?;
            if n > MAX_VIEW_NODES {
                return Err(CodecError::NodeBudgetExceeded(n));
            }
            let mut items = Vec::with_capacity(n);
            for _ in 0..n {
                items.push(Crumb {
                    label: r.read_str()?,
                    turn: r.read_str()?,
                    arg: r.read_i64()?,
                });
            }
            Ok(ViewNode::Breadcrumb { items })
        }
        15 => Ok(ViewNode::Progress {
            value: r.read_u64()?,
            max: r.read_u64()?,
            label: r.read_str()?,
        }),
        16 => {
            let text = r.read_str()?;
            let ptag = r.read_str()?;
            let slot = r.read_opt_usize()?;
            let n = r.read_usize()?;
            if n > MAX_VIEW_NODES {
                return Err(CodecError::NodeBudgetExceeded(n));
            }
            let mut cases = Vec::with_capacity(n);
            for _ in 0..n {
                cases.push(PillCase {
                    value: r.read_u64()?,
                    label: r.read_str()?,
                    tag: r.read_str()?,
                });
            }
            let resolved = r.read_opt_u64()?;
            Ok(ViewNode::Pill {
                text,
                tag: ptag,
                slot,
                cases,
                resolved,
            })
        }
        17 => Ok(ViewNode::Icon {
            glyph: r.read_str()?,
            tag: r.read_str()?,
        }),
        18 => {
            let n = r.read_usize()?;
            if n > MAX_VIEW_NODES {
                return Err(CodecError::NodeBudgetExceeded(n));
            }
            let mut items = Vec::with_capacity(n);
            for _ in 0..n {
                items.push(MenuItem {
                    label: r.read_str()?,
                    turn: r.read_str()?,
                    arg: r.read_i64()?,
                    enabled: r.read_bool()?,
                    wants_text: r.read_bool()?,
                });
            }
            Ok(ViewNode::Menu { items })
        }
        19 => {
            let target_slot = r.read_usize()?;
            let n = r.read_usize()?;
            if n > MAX_VIEW_NODES {
                return Err(CodecError::NodeBudgetExceeded(n));
            }
            let mut handles = Vec::with_capacity(n);
            for _ in 0..n {
                handles.push(HaloHandle {
                    glyph: r.read_str()?,
                    turn: r.read_str()?,
                    arg: r.read_i64()?,
                    enabled: r.read_bool()?,
                });
            }
            Ok(ViewNode::Halo {
                target_slot,
                handles,
            })
        }
        20 => Ok(ViewNode::Slider {
            slot: r.read_usize()?,
            min: r.read_u64()?,
            max: r.read_u64()?,
            turn: r.read_str()?,
            resolved: r.read_opt_u64()?,
        }),
        21 => Ok(ViewNode::Toggle {
            slot: r.read_usize()?,
            on_turn: r.read_str()?,
            off_turn: r.read_str()?,
            glyph_on: r.read_str()?,
            glyph_off: r.read_str()?,
            label: r.read_str()?,
            resolved: r.read_opt_u64()?,
        }),
        22 => Ok(ViewNode::Tile {
            handle: r.read_str()?,
            w: r.read_u32()?,
            h: r.read_u32()?,
        }),
        23 => {
            let cols = r.read_usize()?;
            let n = r.read_usize()?;
            if n > MAX_VIEW_NODES {
                return Err(CodecError::NodeBudgetExceeded(n));
            }
            let mut cells = Vec::with_capacity(n);
            for _ in 0..n {
                cells.push(CoordCell {
                    glyph: r.read_str()?,
                    tag: r.read_str()?,
                    turn: r.read_str()?,
                    arg: r.read_i64()?,
                    highlight: r.read_bool()?,
                });
            }
            Ok(ViewNode::CoordGrid { cols, cells })
        }
        24 => Ok(ViewNode::Adept(Box::new(decode_node(r, depth + 1)?))),
        other => Err(CodecError::InvalidTag("ViewNode", other)),
    }
}

// ---------------------------------------------------------------------------
// Deterministic Tree Diff / Patch (mirrors Lean `diff` / `applyPatch`)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContainerTag {
    VStack,
    Row,
    List,
    Table,
    Section,
    Tabs,
    Grid,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ViewPatch {
    Keep,
    Replace(ViewNode),
    PatchContainer {
        tag: ContainerTag,
        patches: Vec<ViewPatch>,
    },
    PatchHost(Option<Box<ViewPatch>>),
    PatchAdept(Box<ViewPatch>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PatchError {
    ContainerMismatch,
    ArityMismatch { expected: usize, got: usize },
    HostShapeMismatch,
    AdeptShapeMismatch,
}

fn diff_slice(a: &[ViewNode], b: &[ViewNode]) -> Vec<ViewPatch> {
    a.iter().zip(b.iter()).map(|(x, y)| diff(x, y)).collect()
}

/// Deterministic structural tree diff satisfying `apply_patch(v, &diff(v, v')) == Ok(v'.clone())`
/// and `diff(v, v) == ViewPatch::Keep`.
pub fn diff(v: &ViewNode, v_prime: &ViewNode) -> ViewPatch {
    if v == v_prime {
        return ViewPatch::Keep;
    }
    match (v, v_prime) {
        (ViewNode::VStack(a), ViewNode::VStack(b)) if a.len() == b.len() => {
            ViewPatch::PatchContainer {
                tag: ContainerTag::VStack,
                patches: diff_slice(a, b),
            }
        }
        (ViewNode::Row(a), ViewNode::Row(b)) if a.len() == b.len() => ViewPatch::PatchContainer {
            tag: ContainerTag::Row,
            patches: diff_slice(a, b),
        },
        (ViewNode::List(a), ViewNode::List(b)) if a.len() == b.len() => ViewPatch::PatchContainer {
            tag: ContainerTag::List,
            patches: diff_slice(a, b),
        },
        (ViewNode::Table(a), ViewNode::Table(b)) if a.len() == b.len() => {
            ViewPatch::PatchContainer {
                tag: ContainerTag::Table,
                patches: diff_slice(a, b),
            }
        }
        (
            ViewNode::Section {
                title: t1,
                tag: g1,
                children: a,
            },
            ViewNode::Section {
                title: t2,
                tag: g2,
                children: b,
            },
        ) if t1 == t2 && g1 == g2 && a.len() == b.len() => ViewPatch::PatchContainer {
            tag: ContainerTag::Section,
            patches: diff_slice(a, b),
        },
        (
            ViewNode::Tabs {
                tabs: l1,
                selected_slot: s1,
                select_turn: t1,
                resolved_active: r1,
                panels: a,
            },
            ViewNode::Tabs {
                tabs: l2,
                selected_slot: s2,
                select_turn: t2,
                resolved_active: r2,
                panels: b,
            },
        ) if l1 == l2 && s1 == s2 && t1 == t2 && r1 == r2 && a.len() == b.len() => {
            ViewPatch::PatchContainer {
                tag: ContainerTag::Tabs,
                patches: diff_slice(a, b),
            }
        }
        (
            ViewNode::Grid {
                cols: c1,
                children: a,
            },
            ViewNode::Grid {
                cols: c2,
                children: b,
            },
        ) if c1 == c2 && a.len() == b.len() => ViewPatch::PatchContainer {
            tag: ContainerTag::Grid,
            patches: diff_slice(a, b),
        },
        (
            ViewNode::Host {
                cell: c1,
                status: s1,
                view: Some(n1),
            },
            ViewNode::Host {
                cell: c2,
                status: s2,
                view: Some(n2),
            },
        ) if c1 == c2 && s1 == s2 => ViewPatch::PatchHost(Some(Box::new(diff(n1, n2)))),
        (ViewNode::Adept(a), ViewNode::Adept(b)) => ViewPatch::PatchAdept(Box::new(diff(a, b))),
        _ => ViewPatch::Replace(v_prime.clone()),
    }
}

fn apply_slice(nodes: &[ViewNode], patches: &[ViewPatch]) -> Result<Vec<ViewNode>, PatchError> {
    if nodes.len() != patches.len() {
        return Err(PatchError::ArityMismatch {
            expected: nodes.len(),
            got: patches.len(),
        });
    }
    nodes
        .iter()
        .zip(patches.iter())
        .map(|(n, p)| apply_patch(n, p))
        .collect()
}

/// Apply a `ViewPatch`, failing closed on container-tag or arity mismatches.
pub fn apply_patch(v: &ViewNode, patch: &ViewPatch) -> Result<ViewNode, PatchError> {
    match patch {
        ViewPatch::Keep => Ok(v.clone()),
        ViewPatch::Replace(next) => Ok(next.clone()),
        ViewPatch::PatchContainer { tag, patches } => match (tag, v) {
            (ContainerTag::VStack, ViewNode::VStack(cs)) => {
                Ok(ViewNode::VStack(apply_slice(cs, patches)?))
            }
            (ContainerTag::Row, ViewNode::Row(cs)) => Ok(ViewNode::Row(apply_slice(cs, patches)?)),
            (ContainerTag::List, ViewNode::List(cs)) => {
                Ok(ViewNode::List(apply_slice(cs, patches)?))
            }
            (ContainerTag::Table, ViewNode::Table(cs)) => {
                Ok(ViewNode::Table(apply_slice(cs, patches)?))
            }
            (
                ContainerTag::Section,
                ViewNode::Section {
                    title,
                    tag: stag,
                    children,
                },
            ) => Ok(ViewNode::Section {
                title: title.clone(),
                tag: stag.clone(),
                children: apply_slice(children, patches)?,
            }),
            (
                ContainerTag::Tabs,
                ViewNode::Tabs {
                    tabs,
                    selected_slot,
                    select_turn,
                    resolved_active,
                    panels,
                },
            ) => Ok(ViewNode::Tabs {
                tabs: tabs.clone(),
                selected_slot: *selected_slot,
                select_turn: select_turn.clone(),
                resolved_active: *resolved_active,
                panels: apply_slice(panels, patches)?,
            }),
            (ContainerTag::Grid, ViewNode::Grid { cols, children }) => Ok(ViewNode::Grid {
                cols: *cols,
                children: apply_slice(children, patches)?,
            }),
            _ => Err(PatchError::ContainerMismatch),
        },
        ViewPatch::PatchHost(sub_patch) => match (v, sub_patch) {
            (
                ViewNode::Host {
                    cell,
                    status,
                    view: Some(inner),
                },
                Some(p),
            ) => Ok(ViewNode::Host {
                cell: cell.clone(),
                status: status.clone(),
                view: Some(Box::new(apply_patch(inner, p)?)),
            }),
            (
                ViewNode::Host {
                    cell,
                    status,
                    view: None,
                },
                None,
            ) => Ok(ViewNode::Host {
                cell: cell.clone(),
                status: status.clone(),
                view: None,
            }),
            _ => Err(PatchError::HostShapeMismatch),
        },
        ViewPatch::PatchAdept(inner_patch) => match v {
            ViewNode::Adept(inner) => Ok(ViewNode::Adept(Box::new(apply_patch(
                inner,
                inner_patch,
            )?))),
            _ => Err(PatchError::AdeptShapeMismatch),
        },
    }
}

// ---------------------------------------------------------------------------
// Frustum Fog-of-War Observer Scrubber (`Obend.Vault.FrustumMembrane`)
// ---------------------------------------------------------------------------

/// Cut disposition for a hosted cell crossing a viewer's frustum
/// (`obend/lean/Obend/Vault/FrustumMembrane.lean:661`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Disposition {
    Sever { snapshot_digest: u64 },
    Attenuate { allowed_slots: BTreeSet<(String, usize)> },
    Interpose { mock_label: String },
    Tether,
}

#[derive(Debug, Clone)]
pub struct Frustum {
    pub viewer: String,
    pub visible_slots: BTreeSet<(String, usize)>,
    pub policies: BTreeMap<String, Disposition>,
}

impl Frustum {
    pub fn policy_for(&self, cell: &str) -> Disposition {
        self.policies
            .get(cell)
            .cloned()
            .unwrap_or(Disposition::Tether)
    }

    /// Narrow visibility to the intersection with `allowed`.
    pub fn restrict(&self, allowed: &BTreeSet<(String, usize)>) -> Self {
        let visible_slots = self
            .visible_slots
            .intersection(allowed)
            .cloned()
            .collect::<BTreeSet<_>>();
        Self {
            viewer: self.viewer.clone(),
            visible_slots,
            policies: self.policies.clone(),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct WorldState {
    slots: BTreeMap<(String, usize), u64>,
}

impl WorldState {
    pub fn set(&mut self, cell: impl Into<String>, slot: usize, val: u64) {
        self.slots.insert((cell.into(), slot), val);
    }

    pub fn get(&self, cell: &str, slot: usize) -> u64 {
        self.slots.get(&(cell.to_owned(), slot)).copied().unwrap_or(0)
    }
}

fn read_visible_slot(frustum: &Frustum, state: &WorldState, cell: &str, slot: usize) -> Option<u64> {
    if frustum.visible_slots.contains(&(cell.to_owned(), slot)) {
        Some(state.get(cell, slot))
    } else {
        None
    }
}

/// Fog-of-war observer projection matching `LightClientAndViewLens.projectViewNode`.
/// Any slot outside `frustum.visible_slots` is scrubbed (`None`), and `Sever`/`Interpose`
/// hosted cells never consult `state`.
pub fn project_view_node(
    frustum: &Frustum,
    state: &WorldState,
    cur_cell: &str,
    node: &ViewNode,
) -> ViewNode {
    match node {
        ViewNode::VStack(cs) => ViewNode::VStack(
            cs.iter()
                .map(|c| project_view_node(frustum, state, cur_cell, c))
                .collect(),
        ),
        ViewNode::Row(cs) => ViewNode::Row(
            cs.iter()
                .map(|c| project_view_node(frustum, state, cur_cell, c))
                .collect(),
        ),
        ViewNode::List(cs) => ViewNode::List(
            cs.iter()
                .map(|c| project_view_node(frustum, state, cur_cell, c))
                .collect(),
        ),
        ViewNode::Table(rs) => ViewNode::Table(
            rs.iter()
                .map(|c| project_view_node(frustum, state, cur_cell, c))
                .collect(),
        ),
        ViewNode::Section {
            title,
            tag,
            children,
        } => ViewNode::Section {
            title: title.clone(),
            tag: tag.clone(),
            children: children
                .iter()
                .map(|c| project_view_node(frustum, state, cur_cell, c))
                .collect(),
        },
        ViewNode::Tabs {
            tabs,
            selected_slot,
            select_turn,
            panels,
            ..
        } => ViewNode::Tabs {
            tabs: tabs.clone(),
            selected_slot: *selected_slot,
            select_turn: select_turn.clone(),
            resolved_active: read_visible_slot(frustum, state, cur_cell, *selected_slot),
            panels: panels
                .iter()
                .map(|p| project_view_node(frustum, state, cur_cell, p))
                .collect(),
        },
        ViewNode::Grid { cols, children } => ViewNode::Grid {
            cols: *cols,
            children: children
                .iter()
                .map(|c| project_view_node(frustum, state, cur_cell, c))
                .collect(),
        },
        ViewNode::Bind {
            slot, label, fmt, ..
        } => ViewNode::Bind {
            slot: *slot,
            label: label.clone(),
            fmt: *fmt,
            resolved: read_visible_slot(frustum, state, cur_cell, *slot),
        },
        ViewNode::Gauge {
            slot, max, label, ..
        } => ViewNode::Gauge {
            slot: *slot,
            max: *max,
            label: label.clone(),
            resolved: read_visible_slot(frustum, state, cur_cell, *slot),
        },
        ViewNode::Host { cell, view, .. } => match frustum.policy_for(cell) {
            Disposition::Sever { snapshot_digest } => ViewNode::Host {
                cell: cell.clone(),
                status: HostStatus::Severed { snapshot_digest },
                view: None,
            },
            Disposition::Attenuate { allowed_slots } => {
                let narrowed = frustum.restrict(&allowed_slots);
                ViewNode::Host {
                    cell: cell.clone(),
                    status: HostStatus::Attenuated {
                        allowed_count: narrowed.visible_slots.len(),
                    },
                    view: view
                        .as_ref()
                        .map(|v| Box::new(project_view_node(&narrowed, state, cell, v))),
                }
            }
            Disposition::Interpose { mock_label } => ViewNode::Host {
                cell: cell.clone(),
                status: HostStatus::Interposed { mock_label },
                view: None,
            },
            Disposition::Tether => ViewNode::Host {
                cell: cell.clone(),
                status: HostStatus::Live,
                view: view
                    .as_ref()
                    .map(|v| Box::new(project_view_node(frustum, state, cell, v))),
            },
        },
        ViewNode::Pill {
            text,
            tag,
            slot,
            cases,
            ..
        } => ViewNode::Pill {
            text: text.clone(),
            tag: tag.clone(),
            slot: *slot,
            cases: cases.clone(),
            resolved: slot.and_then(|s| read_visible_slot(frustum, state, cur_cell, s)),
        },
        ViewNode::Slider {
            slot,
            min,
            max,
            turn,
            ..
        } => ViewNode::Slider {
            slot: *slot,
            min: *min,
            max: *max,
            turn: turn.clone(),
            resolved: read_visible_slot(frustum, state, cur_cell, *slot),
        },
        ViewNode::Toggle {
            slot,
            on_turn,
            off_turn,
            glyph_on,
            glyph_off,
            label,
            ..
        } => ViewNode::Toggle {
            slot: *slot,
            on_turn: on_turn.clone(),
            off_turn: off_turn.clone(),
            glyph_on: glyph_on.clone(),
            glyph_off: glyph_off.clone(),
            label: label.clone(),
            resolved: read_visible_slot(frustum, state, cur_cell, *slot),
        },
        ViewNode::Adept(inner) => {
            ViewNode::Adept(Box::new(project_view_node(frustum, state, cur_cell, inner)))
        }
        leaf => leaf.clone(),
    }
}

// ---------------------------------------------------------------------------
// Constructive Repair Badge Synthesizer (`Obend.Vault.Affordance:235`)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RefusalBadge {
    pub by_law: String,
    pub reason: String,
    pub missing_caps: Vec<String>,
    pub repair_edits: Option<Vec<(String, u64)>>,
    pub suggestion: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AffordanceStatus {
    Lit { turn: String },
    Dark(RefusalBadge),
}

/// Constructive repair badge synthesizer mirroring `Obend/Vault/Affordance.lean:235-252`.
pub fn synthesize_repair_badge(
    aff_name: &str,
    required_caps: &[String],
    held_caps: &[String],
    law_passed: bool,
    repair_edits: Option<Vec<(String, u64)>>,
    suggestion: &str,
) -> RefusalBadge {
    let missing: Vec<String> = required_caps
        .iter()
        .filter(|req| !held_caps.contains(req))
        .cloned()
        .collect();
    let cap_pass = missing.is_empty();
    if !cap_pass && !law_passed {
        RefusalBadge {
            by_law: aff_name.to_owned(),
            reason: "unauthorized and state contract violated".to_owned(),
            missing_caps: missing,
            repair_edits,
            suggestion: suggestion.to_owned(),
        }
    } else if !cap_pass {
        RefusalBadge {
            by_law: aff_name.to_owned(),
            reason: "unauthorized: missing required capabilities".to_owned(),
            missing_caps: missing,
            repair_edits: None,
            suggestion: String::new(),
        }
    } else if !law_passed {
        RefusalBadge {
            by_law: aff_name.to_owned(),
            reason: "state condition unmet: contract violated".to_owned(),
            missing_caps: Vec::new(),
            repair_edits,
            suggestion: suggestion.to_owned(),
        }
    } else {
        RefusalBadge {
            by_law: aff_name.to_owned(),
            reason: "ok".to_owned(),
            missing_caps: Vec::new(),
            repair_edits: None,
            suggestion: String::new(),
        }
    }
}

pub fn evaluate_affordance(
    aff_name: &str,
    required_caps: &[String],
    held_caps: &[String],
    law_passed: bool,
    repair_edits: Option<Vec<(String, u64)>>,
    suggestion: &str,
) -> AffordanceStatus {
    let badge = synthesize_repair_badge(
        aff_name,
        required_caps,
        held_caps,
        law_passed,
        repair_edits,
        suggestion,
    );
    if badge.reason == "ok" {
        AffordanceStatus::Lit {
            turn: aff_name.to_owned(),
        }
    } else {
        AffordanceStatus::Dark(badge)
    }
}
