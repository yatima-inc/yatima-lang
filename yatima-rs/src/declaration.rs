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
  nat::Nat,
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
pub fn add_inductive_typ(decl: &InductiveDecl, env: &mut Env) -> Result<ConstCid, EnvError> {
  let ind = Const::Inductive {
    name: decl.name.clone(),
    lvl: decl.lvl.clone(),
    typ: decl.typ,
    params: From::from(decl.params.len()),
    indices: From::from(decl.indices.len()),
    ctors: decl.ctors.clone(),
    recr: decl.recr,
    safe: decl.safe,
    // TODO
    refl: false,
    nest: false,
  };
  ind.store(env)
}

#[allow(unused_variables)]
#[inline]
pub fn add_inductive_ctors(decl: &InductiveDecl, ind: ConstCid, param: Nat, safe: bool, env: &mut Env) -> Result<Vec<ConstCid>, EnvError> {
  let mut vec = vec![];
  for (name, typ) in decl.ctors.iter() {
    let ctor = Const::Constructor {
      name: name.clone(),
      // TODO: what should lvl be? Maybe it should be included in the `ctors` field
      lvl: vec![],
      ind,
      typ: *typ,
      param,
      field: todo!(),
      safe,
    };
    let cid = ctor.store(env)?;
    vec.push(cid);
  }
  Ok(vec)
}

#[allow(unused_variables)]
#[inline]
pub fn add_inductive_rules(decl: &InductiveDecl, env: &mut Env) -> Result<ConstCid, EnvError> {
  todo!()
}
