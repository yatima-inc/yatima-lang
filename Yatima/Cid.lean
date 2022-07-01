import Ipld.Cid

namespace Yatima
def UNIVANON  : UInt64 := 0xC0DE0001
def UNIVMETA  : UInt64 := 0xC0DE0002
def EXPRANON  : UInt64 := 0xC0DE0003
def EXPRMETA  : UInt64 := 0xC0DE0004
def CONSTANON : UInt64 := 0xC0DE0005
def CONSTMETA : UInt64 := 0xC0DE0006
def BLOCKANON : UInt64 := 0xC0DE0007
def BLOCKMETA : UInt64 := 0xC0DE0008

def ENV: UInt64 := 0xC0DE0007

structure UnivAnonCid  where data : Cid deriving BEq, Ord
structure UnivMetaCid  where data : Cid deriving BEq, Ord
structure ExprAnonCid  where data : Cid deriving BEq, Ord
structure ExprMetaCid  where data : Cid deriving BEq, Ord
structure ConstAnonCid where data : Cid deriving BEq, Ord
structure ConstMetaCid where data : Cid deriving BEq, Ord
structure BlockAnonCid where data : Cid deriving BEq, Ord
structure BlockMetaCid where data : Cid deriving BEq, Ord

structure UnivCid where 
  anon : UnivAnonCid
  meta : UnivMetaCid
deriving BEq, Ord

structure ExprCid where 
  anon : ExprAnonCid
  meta : ExprMetaCid
deriving BEq, Ord

structure ConstCid where
  anon : ConstAnonCid
  meta : ConstMetaCid
deriving BEq, Ord

structure BlockCid where
  anon : BlockAnonCid
  meta : BlockMetaCid
deriving BEq, Ord

structure EnvCid where data : Cid deriving BEq

instance : ToString UnivAnonCid where toString a := toString a.data
instance : ToString UnivMetaCid where toString a := toString a.data
instance : ToString ExprAnonCid where toString a := toString a.data
instance : ToString ExprMetaCid where toString a := toString a.data
instance : ToString ConstAnonCid where toString a := toString a.data
instance : ToString ConstMetaCid where toString a := toString a.data
instance : ToString BlockAnonCid where toString a := toString a.data
instance : ToString BlockMetaCid where toString a := toString a.data

end Yatima
