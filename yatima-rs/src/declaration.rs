use crate::{
  constant::Const,
  environment::{
    Env,
    EnvError,
    ExprCid,
    ConstCid,
  },
  expression::{
    BinderInfo,
  },
  name::Name,
};

pub struct InductiveDecl {
  pub safe: bool,
  pub recr: bool,
  pub name: Name,
  pub lvl: Vec<Name>,
  pub params: Vec<(BinderInfo, Name, ExprCid)>,
  pub indices: Vec<(BinderInfo, Name, ExprCid)>,
  pub typ: ExprCid,
  pub ctors: Vec<(Name, ExprCid)>,
}

#[inline]
pub fn add_inductive_typ(ind_decl: &InductiveDecl, env: &mut Env) -> Result<ConstCid, EnvError> {
  let ind = Const::Inductive {
    name: ind_decl.name.clone(),
    lvl: ind_decl.lvl.clone(),
    typ: ind_decl.typ,
    params: From::from(ind_decl.params.len()),
    indices: From::from(ind_decl.indices.len()),
    ctors: ind_decl.ctors.clone(),
    recr: ind_decl.recr,
    safe: ind_decl.safe,
    // TODO
    refl: false,
    nest: false,
  };
  ind.store(env)
}

#[allow(unused_variables)]
#[inline]
pub fn add_inductive_ctors(ind: &InductiveDecl, env: &mut Env) {
  todo!()
}

#[allow(unused_variables)]
#[inline]
pub fn add_inductive_rules(ind: &InductiveDecl, env: &mut Env) {
  todo!()
}
