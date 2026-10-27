module

public import CFSG.Quasithin.Recognition.RuRank3TitsSylInputs
public import Certificates.Kernel.SporSch.Tits.PA7051K
import Certificates.Kernel.Sporadic.Tits.Bind2264
import CFSG.Certificates.Kernel.SporSch.OrbRootsSound
import CFSG.Certificates.Kernel.SporSch.RuOrbKGS
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.Glue7051

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KS.OrbLab CFSG.Quasithin.RuRank3
  CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native CertificateChecks.KernelSporSch.PA7051

theorem nat_beq (a b : Nat) : (a == b) = Nat.beq a b := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]

theorem gs : titsPAGens.size = 4 := by simp [titsPAGens]

theorem s_get {j : Nat} (hj : j < 3) {x : Nat} (hx : x < 1755) :
    (titsSArrs[j]!)[x]! = pg 11 (mask 11) (CertificateChecks.KernelMisc.TitsText.F (52 + j)) x := by
  rw [titsSArrs, CertificateChecks.KernelSpor.Tits2264.field_get (by omega) (by norm_num),
    CFSG.KC.BfsPin.unpack_get' hx]

theorem g_get : ∀ k < 4, ∀ x < 1755, (titsPAGens[k]!)[x]! = gP k x := by
  intro k hk x hx
  interval_cases k
  · exact s_get (j := 0) (by norm_num) hx
  · exact s_get (j := 1) (by norm_num) hx
  · exact s_get (j := 2) (by norm_num) hx
  · change (titsGenArrs[1]!)[x]! = _
    rw [CertificateChecks.KernelSpor.Tits2264.gen_eq (by norm_num), CFSG.KC.BfsPin.unpack_get' hx]
    rfl

theorem lab_get {x : Nat} (hx : x < 1755) : titsPALab[x]! = Lf x :=
  (orbLabels_of_K gs g_get kOrb).2 x hx

theorem qr : Mv ≤ 1755 ∧ ∀ t < Mv, Qf t = Rf t := by
  obtain ⟨h1, h2⟩ := (CFSG.KS.bAnd_iff (Nat.ble Mv 1755)
    (allN Mv (fun t => Nat.beq (Qf t) (Rf t)))).1 kQR
  exact ⟨Nat.ble_eq.mp h1, fun t ht => Nat.eq_of_beq_eq_true (allN_spec h2 t ht)⟩

theorem orb_ok : orbCheck 1755 titsPAGens = true := by
  unfold orbCheck
  obtain ⟨r1, r2⟩ := orbRoots_of_K gs g_get kOrb
  exact orbitPartOK_forestKG (by norm_num) gs g_get
    ⟨r1, fun t ht => by rw [r2 t ht, qr.2 t ht]⟩ qr.1 (fun x hx => lab_get hx)
    (fun t ht => allN_spec kF t ht) (fun e he => allN_spec kE e (by omega))
    (fun x hx => allN_spec kP x hx) (fun k hk => allN_spec kRt k hk)

theorem labCount_eq (c : Nat) : ∀ n, n ≤ 1755 → labCount n titsPALab c = cntL n c
  | 0, _ => rfl
  | n + 1, hn => by
    have e1 : labCount (n + 1) titsPALab c =
        labCount n titsPALab c + if (titsPALab[n]! == c) = true then 1 else 0 := by
      simp [labCount, List.range_succ, List.countP_append]
    change _ = Bool.rec (motive := fun _ => Nat) (cntL n c) (Nat.succ (cntL n c))
      (Nat.beq (Lf n) c)
    rw [e1, labCount_eq c n (by omega), lab_get (by omega), nat_beq]
    cases h : Nat.beq (Lf n) c <;> simp

theorem cnt_lab {x : Nat} (hx : x < 1755) :
    labCount 1755 titsPALab titsPALab[x]! = cntL 1755 (Lf x) := by
  rw [labCount_eq _ 1755 le_rfl, lab_get hx]

theorem big {x : Nat} (hx : x < 1755) (h3 : 3 ≤ x) : 8 ≤ cntL 1755 (Lf x) := by
  have ho := allN_spec kOut x hx
  beta_reduce at ho
  have hlt : Nat.blt x 3 = false := by
    cases h : Nat.blt x 3
    · rfl
    · exact absurd (Nat.blt_eq.mp h) (by omega)
  rw [hlt] at ho
  obtain ⟨h0, h1⟩ := (CFSG.KS.bAnd_iff (bIf(Nat.beq (Lf x) (Lf 0), false, true))
    (bIf(Nat.beq (Lf x) (Lf 1), false, true))).1 ho
  have h0' : Nat.beq (Lf x) (Lf 0) = false := by
    cases h : Nat.beq (Lf x) (Lf 0)
    · rfl
    · rw [h] at h0
      exact absurd h0 (by decide)
  have h1' : Nat.beq (Lf x) (Lf 1) = false := by
    cases h : Nat.beq (Lf x) (Lf 1)
    · rfl
    · rw [h] at h1
      exact absurd h1 (by decide)
  have hb := allN_spec kBig (Lf x) (Nat.blt_eq.mp (allN_spec kLt x hx))
  beta_reduce at hb
  rw [h0', h1'] at hb
  exact Nat.ble_eq.mp hb

theorem fix0 : (titsGenArrs[1]!)[0]! = 0 := by
  rw [CertificateChecks.KernelSpor.Tits2264.gen_eq (by norm_num),
    CFSG.KC.BfsPin.unpack_get' (by norm_num)]
  exact Nat.eq_of_beq_eq_true kFix

open Certificates in
open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier in
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates in
theorem c7051 :
    orbCheck 1755 titsPAGens = true ∧ labCount 1755 titsPALab titsPALab[0]! = 1 ∧
      titsPALab[1]! = titsPALab[2]! ∧ labCount 1755 titsPALab titsPALab[1]! = 2 ∧
      (allLt 1755 fun x => x == 0 || x == 1 || x == 2 ||
        decide (8 ≤ labCount 1755 titsPALab titsPALab[x]!)) = true ∧
      (titsGenArrs[1]!)[0]! = 0 := by
  obtain ⟨c0, h⟩ := (CFSG.KS.bAnd_iff (Nat.beq (cntL 1755 (Lf 0)) 1)
    bAnd(Nat.beq (Lf 1) (Lf 2), Nat.beq (cntL 1755 (Lf 1)) 2)).1 kCnt
  obtain ⟨c12, c1⟩ := (CFSG.KS.bAnd_iff (Nat.beq (Lf 1) (Lf 2))
    (Nat.beq (cntL 1755 (Lf 1)) 2)).1 h
  refine ⟨orb_ok, ?_, ?_, ?_, CFSG.Monster.B.Co2.allLt_iff.2 fun x hx => ?_, fix0⟩
  · rw [cnt_lab (by norm_num)]
    exact Nat.eq_of_beq_eq_true c0
  · rw [lab_get (by norm_num), lab_get (by norm_num)]
    exact Nat.eq_of_beq_eq_true c12
  · rw [cnt_lab (by norm_num)]
    exact Nat.eq_of_beq_eq_true c1
  · by_cases h3 : x < 3
    · interval_cases x <;> rfl
    · rw [cnt_lab hx]
      have := big hx (by omega)
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
      exact Or.inr this

end CertificateChecks.KernelSporSch.Glue7051

end
