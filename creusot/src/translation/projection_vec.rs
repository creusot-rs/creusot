use rustc_middle::mir::ProjectionElem;

pub(super) type ProjectionVec<V, T> = Vec<ProjectionElem<V, T>>;

pub(super) fn visit_projections<V, T>(v: &ProjectionVec<V, T>, mut f: impl FnMut(&V)) {
    v.iter().for_each(|elem| match elem {
        ProjectionElem::Index(v) => f(v),
        _ => {}
    })
}

pub(super) fn visit_projections_mut<V, T>(v: &mut ProjectionVec<V, T>, mut f: impl FnMut(&mut V)) {
    v.iter_mut().for_each(|elem| match elem {
        ProjectionElem::Index(v) => f(v),
        _ => {}
    })
}

pub(crate) fn map_projections<'a, V, T, W>(
    v: impl Iterator<Item = ProjectionElem<V, T>> + 'a,
    mut f: impl FnMut(V) -> W + 'a,
) -> impl Iterator<Item = ProjectionElem<W, T>> + 'a {
    v.into_iter().map(move |elem: ProjectionElem<V, T>| match elem {
        ProjectionElem::Deref => ProjectionElem::Deref,
        ProjectionElem::Field(idx, t) => ProjectionElem::Field(idx, t),
        ProjectionElem::Index(v) => ProjectionElem::Index(f(v)),
        ProjectionElem::ConstantIndex { offset, min_length, from_end } => {
            ProjectionElem::ConstantIndex { offset, min_length, from_end }
        }
        ProjectionElem::Subslice { from, to, from_end } => {
            ProjectionElem::Subslice { from, to, from_end }
        }
        ProjectionElem::Downcast(s, v) => ProjectionElem::Downcast(s, v),
        ProjectionElem::OpaqueCast(t) => ProjectionElem::OpaqueCast(t),
    })
}
