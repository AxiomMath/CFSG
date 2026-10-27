module

public import Certificates.Kernel.SporSch.Ru.Gens
public import CFSG.Quasithin.Vol2.KGFactG2RuInputs
public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.G2Ru7164

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelSporSch.RuG
  CFSG.Quasithin.H13.Ch4.G2Ru

@[expose] noncomputable def pc (a b : Nat) : Nat := pcomp 4060 12 (mask 12) a b

@[expose] noncomputable def pinv (a : Nat) : Nat := pinvS 4060 12 (mask 12) a

@[expose] noncomputable def pid : Nat := pidn 4060 12

@[expose] noncomputable def letK (G : Nat → Nat) (l : Int) : Nat :=
  Bool.rec (motive := fun _ => Nat) (pinv (G ((-l).toNat - 1))) (G (l.toNat - 1)) (decide (0 < l))

@[expose] noncomputable def wK (G : Nat → Nat) (w : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) pid (fun l _ ih => pc (letK G l) ih) w

@[expose] noncomputable def Cf (j : Nat) : Nat := Bool.rec (motive := fun _ => Nat) C1 C0 (Nat.beq j 0)

@[expose] noncomputable def WG (k : Nat) : Nat := wK SG (g2WWords.getD k [])

@[expose] noncomputable def VG (k : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (wK SG (g2VWords.getD (k - 1) [])) (WG 0) (Nat.beq k 0)

@[expose] noncomputable def powK (t e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) pid (fun _ ih => pc t ih) e

@[expose] noncomputable def WPk (e : Nat) : Nat :=
  pc (powK (WG 0) (e % 2)) (pc (powK (WG 1) (e / 2 % 2)) (pc (powK (WG 2) (e / 4 % 2))
    (pc (powK (WG 3) (e / 8 % 2)) (pc (powK (WG 4) (e / 16 % 2)) (powK (WG 5) (e / 32 % 2))))))

@[expose] noncomputable def VPk (e : Nat) : Nat :=
  pc (powK (VG 0) (e % 2)) (pc (powK (VG 1) (e / 2 % 2)) (powK (VG 2) (e / 4 % 2)))

@[expose] noncomputable def inWK (T : Nat) : Bool := (List.range 64).any fun e => Nat.beq T (WPk e)

@[expose] noncomputable def inVK (T : Nat) : Bool := (List.range 8).any fun e => Nat.beq T (VPk e)

@[expose] noncomputable def conjK (t u : Nat) : Nat := pc (pc t u) (pinv t)

@[expose] noncomputable def normWK (t : Nat) : Bool := (List.range 6).all fun k => inWK (conjK t (WG k))
@[expose] noncomputable def normVK (t : Nat) : Bool := (List.range 3).all fun k => inVK (conjK t (VG k))
@[expose] noncomputable def centWK (t : Nat) : Bool :=
  (List.range 6).all fun k => Nat.beq (conjK t (WG k)) (WG k)
@[expose] noncomputable def centVK (t : Nat) : Bool :=
  (List.range 3).all fun k => Nat.beq (conjK t (VG k)) (VG k)
@[expose] noncomputable def sameWK (t u : Nat) : Bool :=
  (List.range 6).all fun k => Nat.beq (conjK t (WG k)) (conjK u (WG k))

@[expose] noncomputable def NAk (j : Nat) : Nat := wK Cf (g2NWords.getD j [])
@[expose] noncomputable def XAk : Nat := wK Cf g2XWord
@[expose] noncomputable def AAk (i : Nat) : Nat := wK Cf (g2AWords.getD i [])

@[expose] noncomputable def commK (t u : Nat) : Nat := pc (conjK t u) (pinv u)

@[expose] noncomputable def DAk (m : Nat) : Nat :=
  pc (VG (g2DIdx.getD m (0, 0)).2) (conjK (pinv (NAk (g2DIdx.getD m (0, 0)).1)) (VG (g2DIdx.getD m (0, 0)).2))

@[expose] noncomputable def DPk (e : Nat) : Nat :=
  pc (powK (DAk 0) (e % 2)) (pc (powK (DAk 1) (e / 2 % 2)) (powK (DAk 2) (e / 4 % 2)))
@[expose] noncomputable def APk (e : Nat) : Nat :=
  pc (powK (AAk 0) (e % 2)) (pc (powK (AAk 1) (e / 2 % 2)) (powK (AAk 2) (e / 4 % 2)))

theorem kPerm : bAnd(permOK 4060 12 (mask 12) (4060 * 12) C0 (pinv C0),
    bAnd(permOK 4060 12 (mask 12) (4060 * 12) C1 (pinv C1),
    (List.range 4).all fun j => permOK 4060 12 (mask 12) (4060 * 12) (SG j) (pinv (SG j)))) = true := by
  quickRfl

theorem k1 : centVK XAk = true := by quickRfl
theorem k2 : (!normWK XAk) = true := by quickRfl
theorem k3 : (List.range 2).all (fun j => normWK (NAk j) && normVK (NAk j) &&
    normWK (commK (NAk j) XAk)) = true := by quickRfl
theorem k4 : (List.range 3).all (fun m => inVK (DAk m)) = true := by quickRfl
theorem k5 : (List.range 8).all (fun i => (List.range 8).all fun j =>
    !decide (i < j) || !Nat.beq (DPk i) (DPk j)) = true := by quickRfl
theorem k6 : (List.range 3).all (fun i => normWK (AAk i) && centVK (AAk i) &&
    centWK (pc (AAk i) (AAk i))) = true := by quickRfl
theorem k7 : (List.range 3).all (fun i => (List.range 3).all fun j =>
    sameWK (pc (AAk i) (AAk j)) (pc (AAk j) (AAk i))) = true := by quickRfl
theorem k8 : (List.range 8).all (fun e => (List.range 8).all fun e' =>
    !decide (e < e') || !sameWK (APk e) (APk e')) = true := by quickRfl

theorem neg : ((!centWK XAk) && !inWK (NAk 0) && !Nat.beq (pc (AAk 0) (AAk 1)) (AAk 1)) = true := by
  quickRfl

end CertificateChecks.KernelSporSch.G2Ru7164

end
