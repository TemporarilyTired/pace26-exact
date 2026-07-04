use super::arena_vertex::Label;

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum PerformedReduction {
    SvtRemoved {
        label: Label,
    },
    LabelsMerged {
        original1: Label,
        original2: Label,
        new_label: Label,
    },
}
