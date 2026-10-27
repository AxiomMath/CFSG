module

public import Certificates.Kernel.GMS78.CzJS
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelGMS78.CzJ

open CFSG.KC.GMS CFSG.KLie.CT CFSG.ComponentClassification.GMS78.RuCz CFSG.Monster.B.Fischer
  CFSG.RankThree.Native

@[expose] def HTL : List (List ℕ) :=
  (List.range 6).map fun i => invCodes ((czHCodes.getD i []).drop 3)

theorem t_points : kPoints czT128P.toList PT czJCertP = true := by quickRfl

@[expose] noncomputable def ptF (i : Nat) : Bool := kPointAt czT128P.toList PT LK PAR LAB i

#lc_blocks ptB ptF 2048 64

theorem t_keys : kKeys PT = true := by quickRfl

theorem t_cols : kCols czJCertP LK = true := by quickRfl

theorem t_parlab : kParLab czJCertP PAR LAB = true := by quickRfl

@[expose] noncomputable def rowF (a : Nat) : Bool := kRow LK RW PAR LAB a

#lc_blocks rowB rowF 2048 64

@[expose] noncomputable def invF (a : Nat) : Bool := kInv RW INV a

#lc_blocks invB invF 2048 2048

theorem t_prep : kPrep RW PAR LAB INV GIL czWq czWw czSols KQ KW FIX D3 D5 CT SOLS = true := by
  quickRfl

theorem t_ident : kIdent RW PAR LAB INV GIL czRelsJ czWq czWv czWw czNormX c2JCodes HTL
    (czHCodes.drop 7) czSols czClass2To1 = true := by
  quickRfl

theorem czT128_eq : czT128 = (czT128P.toList.map czUnpack).toArray := by rfl

end CertificateChecks.KernelGMS78.CzJ

end
