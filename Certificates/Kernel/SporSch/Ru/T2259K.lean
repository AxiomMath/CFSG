module

public import Certificates.Kernel.SporSch.Ru.TreePL
public import Certificates.Kernel.SporSch.Ru.TreeData
public import Certificates.Kernel.SporSch.Ru.Gens
public import CFSG.Certificates.Kernel.LieCocycle.Fi22.NwValid
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Ru2259

open CFSG.KC.Enum CFSG.KS CFSG.KS.RuTree CFSG.KLC.Fi22 CertificateChecks.KernelSporSch
  CertificateChecks.KernelSporSch.RuTree

@[expose] noncomputable def blk (i : Nat) : Bool :=
  blockK RuTD.NW0 RuTD.NW1 RuTD.F0 plK RuTD.FC RuTD.T RuTD.D (nat_lit 659760) (nat_lit 118755)
    (RuTD.BND i) (Nat.sub (RuTD.BND (Nat.succ i)) (RuTD.BND i))

@[expose] noncomputable def pblk (i : Nat) : Bool :=
  rngK (Nat.mul (nat_lit 4096) i) (nat_lit 4096)
    (fun j => orB (notB (Nat.blt j (nat_lit 593775))) (partK RuTD.FC j))

@[expose] noncomputable def arrK (NW A : Nat) : Bool :=
  rngK (nat_lit 0) (nat_lit 4096) (fun s => (fun v =>
    andB (Nat.beq v (Bool.rec (motive := fun _ => Nat) s (pg 12 (mask 12) A s) (Nat.blt s (nat_lit 4060))))
      (orB (notB (Nat.blt s (nat_lit 4060))) (Nat.blt v (nat_lit 4060))))
    (Nat.land (Nat.shiftRight (arrInvNW NW) (Nat.mul (nat_lit 16) s)) (nat_lit 65535)))

@[expose] noncomputable def fixL (Z : Nat) (n : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) [] (fun p ih =>
    Bool.rec (motive := fun _ => List Nat) ih (List.append ih [p]) (Nat.beq (pg 12 (mask 12) Z p) p)) n

@[expose] noncomputable def lenK (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def mskK (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun p _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) p) ih) l

theorem nw0 : nwValid RuTD.NW0 = true := by quickRfl
theorem nw1 : nwValid RuTD.NW1 = true := by quickRfl
theorem arr0 : arrK RuTD.NW0 RuG.A0 = true := by quickRfl
theorem arr1 : arrK RuTD.NW1 RuG.A1 = true := by quickRfl
theorem fix92 : Nat.beq (lenK (fixL RuG.Z 4060)) 92 = true := by quickRfl
theorem f0 : Nat.beq (Nat.shiftRight RuTD.F0 4096) (mskK (fixL RuG.Z 4060)) = true := by quickRfl
theorem fc0 : Nat.beq (fcK RuTD.FC 0) 1 = true := by quickRfl
theorem fcN : Nat.beq (fcK RuTD.FC 593775) 593775 = true := by quickRfl
theorem cut0 : cutK RuTD.FC 0 = true := by quickRfl
theorem bnd0 : Nat.beq (RuTD.BND 0) 0 = true := by quickRfl
theorem bndK : Nat.beq (RuTD.BND 232) 593775 = true := by quickRfl
theorem bndMono : rngK 0 232 (fun i => Nat.ble (RuTD.BND i) (RuTD.BND (Nat.succ i))) = true := by
  quickRfl

theorem negChk : (!chkK RuTD.T RuTD.D 659760 118755 1 RuTD.F0) = true := by quickRfl

theorem negArr : (!arrK RuTD.NW0 RuG.A1) = true := by quickRfl

theorem negF0 : (!Nat.beq (Nat.shiftRight (Nat.lor RuTD.F0 (Nat.shiftLeft 1 (4096 + 4059))) 4096)
    (mskK (fixL RuG.Z 4060))) = true := by quickRfl

end CertificateChecks.KernelSporSch.Ru2259

end
