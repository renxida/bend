pub mod hvmc_to_net;
pub mod net_to_hvmc;

use crate::term::DefId;
use hvmc::run::Lab;
use NodeKind::*;

#[derive(Clone, Debug)]
/// Net representation used only as an intermediate for converting to hvm-core format
pub struct INet {
  nodes: Vec<Node>,
}

#[derive(Debug, Clone)]
pub struct Node {
  pub main: Port,
  pub aux1: Port,
  pub aux2: Port,
  pub kind: NodeKind,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Port(pub NodeId, pub SlotId);

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NodeKind {
  /// Root node
  Rot,
  /// Erasure nodes
  Era,
  /// Lambdas and applications
  Con {
    lab: Option<Lab>,
  },
  Tup,
  Dup {
    lab: Lab,
  },
  /// Reference to function definitions
  Ref {
    def_id: DefId,
  },
  /// Numbers
  Num {
    val: u64,
  },
  /// Numeric operations
  Op2 {
    opr: hvmc::ops::Op,
  },
  /// Pattern matching on numbers
  Mat,
}

pub type NodeId = u64;
pub type SlotId = u64;

/// The ROOT port is on the deadlocked root node at address 0.
pub const ROOT: Port = Port(0, 1);
pub const TAG_WIDTH: u32 = 4;
pub const TAG: u32 = u64::BITS - TAG_WIDTH;
pub const LABEL_MASK: u64 = (1 << TAG) - 1;
pub const TAG_MASK: u64 = !LABEL_MASK;

impl INet {
  /// Create a new net, with a deadlocked root node.
  pub fn new() -> Self {
    Self::default()
  }

  /// Allocates a new node with its ports disconnected.
  pub fn new_node(&mut self, kind: NodeKind) -> NodeId {
    let idx = self.nodes.len() as NodeId;
    let node = Node::new(Port(idx, 0), Port(idx, 1), Port(idx, 2), kind);
    self.nodes.extend([node]);
    idx
  }

  /// Returns a copy of a node.
  pub fn node(&self, node: NodeId) -> Node {
    self.nodes[node as usize].clone()
  }

  /// Returns the value stored at a port, the port on the other side of the given one.
  pub fn enter_port(&self, port: Port) -> Port {
    self.node(port.node()).port(port.slot())
  }

  /// Links two ports.
  pub fn link(&mut self, a: Port, b: Port) {
    self.set(a, b);
    self.set(b, a);
  }

  /// Sets a port to point to another port
  pub fn set(&mut self, src: Port, dst: Port) {
    *self.nodes[src.node() as usize].port_mut(src.slot()) = dst;
  }
}

impl Default for INet {
  fn default() -> Self {
    INet {
      nodes: vec![Node::new(Port(0, 2), Port(0, 1), Port(0, 0), Rot)], // p2 points to p0, p1 points to net
    }
  }
}

impl Node {
  pub fn new(main: Port, aux1: Port, aux2: Port, kind: NodeKind) -> Self {
    Node { main, aux1, aux2, kind }
  }

  pub fn port(&self, slot: SlotId) -> Port {
    match slot {
      0 => self.main,
      1 => self.aux1,
      2 => self.aux2,
      _ => unreachable!(),
    }
  }

  pub fn port_mut(&mut self, slot: SlotId) -> &mut Port {
    match slot {
      0 => &mut self.main,
      1 => &mut self.aux1,
      2 => &mut self.aux2,
      _ => unreachable!(),
    }
  }
}

impl Port {
  /// Returns the node address of a port.
  pub fn node(self) -> NodeId {
    self.0
  }

  /// Returns the slot of a port.
  pub fn slot(self) -> SlotId {
    self.1
  }
}

/* INodes representation: */

/// A flat inet representation where links are represented by shared wire names.
// TODO: Find a better name
pub type INodes = Vec<INode>;

#[derive(Debug)]
pub struct INode {
  pub kind: NodeKind,
  pub ports: [String; 3],
}
