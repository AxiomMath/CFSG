module

public import Certificates.Kernel.SchreierFam.Ru7234S
public import Certificates.Kernel.SchreierFam.Ru7234X
public import Certificates.Kernel.SchreierFam.Ru7234D
public import Certificates.Kernel.RuInsp443.Checks
public import Certificates.Data.Kernel.Misc.M64Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSchreierFam.Ru7234

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.RuInsp CFSG.KC.Misc.M64
  CFSG.Quasithin.KGC31.Ru CertificateChecks.KernelRuInsp CertificateChecks.KernelSporSch.RuG

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 4060 12 (mask 12) p q

@[expose] noncomputable def ID : Nat := pidn 4060 12

@[expose] noncomputable def S (j : Nat) : Nat := Ru7234S.S j

@[expose] noncomputable def SI (j : Nat) : Nat := Ru7234S.SI j

@[expose] noncomputable def BL : List Nat := [BB 0, BB 1, BB 2, BB 3, BB 4, BB 5]

@[expose] noncomputable def G11 (l : Nat) : Nat := nIf(Nat.blt l 5, UU l, BB (l - 5))

@[expose] noncomputable def G11I (l : Nat) : Nat := nIf(Nat.blt l 5, UU (5 + l), BB (l + 1))

@[expose] noncomputable def MT (i : Nat) : Nat := nIf(Nat.blt i 6, BB i, UU (i - 6))

@[expose] noncomputable def wS (wd : List Int) : Nat := wordK 4060 12 (mask 12) ID S SI wd

@[expose] noncomputable def conjOK (i k : Nat) : Bool :=
  strictB (wS (conjT64W.getD i [])) fun c => strictB (wS (invW (conjT64W.getD i []))) fun ci =>
    bAnd(Nat.blt i 63, bAnd(wordEqK 4060 12 (mask 12) ID S SI 5 (conjT64W.getD i []) c,
      bAnd(wordEqK 4060 12 (mask 12) ID S SI 5 (invW (conjT64W.getD i [])) ci,
      bAnd(permOK 4060 12 (mask 12) (4060 * 12) c ci,
      bAnd(cn c, bAnd(cn ci, Nat.beq (pc (pc c (TT 0)) ci) (SP k)))))))

theorem kP : allN 5 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (S j) (SI j)) = true := by
  quickRfl

theorem kS : allN 5 (fun j => wd6 (strongM64W.getD j []) (S j)) = true := by quickRfl

theorem kSX : allN 5 (fun j => Nat.beq (Ru7234X.S j) (S j)) = true := by quickRfl

theorem kBase : bAnd(allN 2 (fun t => Nat.beq (#[0, 1] : Array Nat)[t]! (pg 12 (mask 12) Ru7234S.BP t)),
    allN 4 (fun t => Nat.beq (#[0, 1, 2, 3] : Array Nat)[t]! (pg 12 (mask 12) Ru7234X.BP t))) =
    true := by quickRfl

theorem kLast : allN 2 (fun i => Nat.beq (rcnt (Ru7234X.LR (Nat.add 2 i))) 1) = true := by quickRfl

theorem kProd : ((List.range 2).map fun i => rcnt (Ru7234S.LR i)).prod = 387072 := by
  decide +kernel

theorem kB : allN 6 (fun j => bAnd(wd6 (basis64W.getD j []) (BB j),
    permOK 4060 12 (mask 12) (4060 * 12) (BB j) (BB (6 + j)))) = true := by quickRfl

theorem kU : allN 5 (fun j => bAnd(wd6 (u33W.getD j []) (UU j),
    permOK 4060 12 (mask 12) (4060 * 12) (UU j) (UU (5 + j)))) = true := by quickRfl

theorem kT : wd6 t64W (TT 0) = true := by quickRfl

theorem kSP : allN 64 (fun k => Nat.beq (SP k) (maskL 4060 12 (mask 12) ID BL k)) = true := by
  quickRfl

theorem kCn : bAnd(allN 5 (fun j => bAnd(cn (S j), cn (SI j))),
    bAnd(allN 12 (fun j => cn (BB j)), bAnd(allN 10 (fun j => cn (UU j)),
    bAnd(cn (TT 0), bAnd(allN 64 (fun k => cn (SP k)), bAnd(cn ID, bAnd(idK 4060 12 (mask 12),
    Nat.beq (SP 0) ID))))))) = true := by quickRfl

theorem kNorm : allN 5 (fun j => allN 6 (fun i => bAnd(Nat.blt (nIdx.getD (6 * j + i) 64) 64,
    Nat.beq (pc (pc (S j) (BB i)) (SI j)) (SP (nIdx.getD (6 * j + i) 64))))) = true := by
  quickRfl

theorem kRel : ((List.range 15).all fun t => bAnd(Nat.blt (rIdx.getD t 64) 64,
    Nat.beq (relK 4060 12 (mask 12) ID UU (CFSG.Quasithin.u33PresRels.getD t []))
      (SP (rIdx.getD t 64)))) = true := by
  decide +kernel

theorem kMem : allN 11 (fun i =>
    wordEqK 4060 12 (mask 12) ID S SI 5 (memL.getD i []) (MT i)) = true := by quickRfl

theorem kG11 : allN 11 (fun l => permOK 4060 12 (mask 12) (4060 * 12) (G11 l) (G11I l)) = true := by
  quickRfl

theorem kIn : allN 5 (fun j =>
    wordEqK 4060 12 (mask 12) ID G11 G11I 11 (strongInU33W.getD j []) (S j)) = true := by quickRfl

theorem kConj : allN 63 (fun k => conjOK (cIdx.getD (k + 1) 63) (k + 1)) = true := by quickRfl

end CertificateChecks.KernelSchreierFam.Ru7234

end
