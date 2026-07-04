use pace26io::binary_tree::{IndexedBinTree, TopDownCursor};

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Status {
    Present,
    MergedIntoParent, // only applicable on leaves
    Contracted,       // only applicable on inner nodes
    Removed,          // node can be ignored
}
use Status::*;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NodeData {
    Internal { left: Idx, right: Idx }, // internal nodes have 2 children
    Leaf { label: Label },              // leaf nodes have no children, but one label
}
use NodeData::*;

pub type Idx = u16;

#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Label(pub Idx);

// Vertex enum for tree/forest stored as contiguous vector
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Node {
    pub status: Status,
    pub data: NodeData,
    pub parent: Option<Idx>, // parent
}

impl Node {
    pub fn new_from_indexed_bin_tree(
        node: &IndexedBinTree,
        children: Option<(Idx, Idx)>,
        parent: Option<Idx>,
    ) -> Node {
        match &node {
            IndexedBinTree::Node(boxed_values) => {
                let (pace26io::binary_tree::NodeIdx(_node_idx), _, _) = **boxed_values;
                let (left, right) = children.expect(
                    "When constructing Node from IndexedBinTree::Node, we expect two children",
                );

                Node {
                    status: Present,
                    data: Internal { left, right },
                    parent,
                }
            }
            IndexedBinTree::Leaf(pace26io::binary_tree::Label(label)) => Node {
                status: Present,
                data: Leaf {
                    label: Label(
                        Idx::try_from(*label)
                            .expect("Expected label to be at most the max size of Idx type (u16)"),
                    ),
                },
                parent,
            },
        }
    }

    #[inline]
    pub fn label(&self) -> Option<Label> {
        match self.data {
            Leaf { label } => Some(label),
            _ => None,
        }
    }

    #[inline]
    pub fn convert_to_leaf(&mut self, label: Label) {
        assert!(
            matches!(self.data, Internal { .. }),
            "Expected a non-leaf when converting to a leaf"
        );
        self.data = Leaf { label };
    }

    #[inline]
    pub fn children(&self) -> impl Iterator<Item = Idx> + use<> {
        match &self.data {
            Internal { left, right } => vec![*left, *right].into_iter(),
            _ => vec![].into_iter(),
        }
    }

    pub fn replace_child(
        &mut self,
        old_child_idx: Idx,
        new_child_idx: Idx,
    ) -> Result<(), &'static str> {
        let Internal { left, right } = &mut self.data else {
            return Err("Error: Cannot replace child of a leaf");
        };
        if *left == old_child_idx {
            *left = new_child_idx;
            return Ok(());
        }
        if *right == old_child_idx {
            *right = new_child_idx;
            return Ok(());
        }

        Err("Could not replace child: requested child not present in node")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ArenaVertexTopDown<'a> {
    pub idx: usize,
    pub arena: &'a Vec<Node>,
}

impl<'a> ArenaVertexTopDown<'a> {
    pub fn new(idx: usize, arena: &'a Vec<Node>) -> Self {
        assert!(idx < arena.len());
        assert!(matches!(arena[idx].status, Present));
        Self { idx, arena }
    }

    pub fn vertex(&self) -> &'a Node {
        &self.arena[self.idx]
    }
}

impl<'a> TopDownCursor for ArenaVertexTopDown<'a> {
    fn children(&self) -> Option<(Self, Self)> {
        assert!(matches!(
            self.vertex(),
            Node {
                status: Present,
                ..
            }
        ));
        match self.vertex() {
            &Node {
                data: Internal { left, right },
                ..
            } => Some((
                ArenaVertexTopDown::new(left as usize, self.arena),
                ArenaVertexTopDown::new(right as usize, self.arena),
            )),
            _ => None,
        }
    }

    fn leaf_label(&self) -> Option<pace26io::binary_tree::Label> {
        match self.vertex().data {
            Leaf { label } => Some(pace26io::binary_tree::Label(label.0 as u32)),
            _ => None,
        }
    }
}
