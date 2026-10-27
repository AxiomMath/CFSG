module

public import Certificates.Data.HNG3Order
public import Certificates.Kernel.SporSch.HN.Strong
public import Certificates.Kernel.SporSch.HN.G3K
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.SporSch.HNF5KronSound
import CFSG.Certificates.Kernel.PackSetSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNG3

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.He.Native CFSG.Sporadic.HNSchreier.Native
open CFSG.Sporadic.HNSchreier CertificateChecks.KernelSporSch
open CFSG.HardMathSupport.Solomon.Coordinator.HN3

theorem entK {K : Nat} (hK : K < 86) : Canon5 (sg K) ∧
    (HNG.OP K = 0 → Canon5 (sg (HNG.L K)) → Canon5 (sg (HNG.R K)) →
      ∀ i < 133, vm5 (sg (HNG.R K)) (sg (HNG.L K) i) = sg K i) ∧
    (HNG.OP K = 1 → ∀ i < 133, sg (HNG.L K) i = sg K i) := by
  rcases (by omega : K < 37 ∨ (37 ≤ K ∧ K < 47) ∨ (47 ≤ K ∧ K < 57) ∨ (57 ≤ K ∧ K < 67) ∨
      (67 ≤ K ∧ K < 77) ∨ 77 ≤ K) with h | h | h | h | h | h
  · exact F5Kron.krBlk_sound blk0 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk1 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk2 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk3 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk4 (by omega) (by omega)
  · exact F5Kron.krBlk_sound blk5 (by omega) (by omega)

theorem canon (k : Nat) (hk : k < 86) : Canon5 (sg k) := (entK hk).1

theorem mulG {K l r : Nat} (hK : K < 86) (ho : HNG.OP K = 0) (hl : HNG.L K = l)
    (hr : HNG.R K = r) : ∀ i < 133, vm5 (sg r) (sg l i) = sg K i := by
  subst hl hr
  have hs := CFSG.KC.Pack.allN_spec specLt K hK
  rw [CFSG.KC.Pack.band_iff, Nat.blt_eq, Nat.blt_eq] at hs
  exact (entK hK).2.1 ho (canon _ hs.1) (canon _ hs.2)

theorem copyG {K l : Nat} (hK : K < 86) (ho : HNG.OP K = 1) (hl : HNG.L K = l) :
    ∀ i < 133, sg l i = sg K i := by
  subst hl
  exact (entK hK).2.2 ho

theorem mul_eq {K l r : Nat} (hl1 : l < 86) (hr1 : r < 86) (hK : K < 86) (ho : HNG.OP K = 0)
    (hl : HNG.L K = l) (hr : HNG.R K = r) :
    mulM 5 133 (rows5 (sg l)) (rows5 (sg r)) = rows5 (sg K) :=
  mulM5_sound (canon l hl1) (canon r hr1) (mulG hK ho hl hr)

@[expose] def letRk (l : Nat) : Nat := if l = 1 then 0 else 1

@[expose] noncomputable def rootB : Bool :=
  FAData.g3Root.length == 22 && HNG.OP 37 == 1 && HNG.L 37 == letRk (FAData.g3Root.headD 0) &&
    (List.range 21).all fun u => HNG.OP (38 + u) == 0 && HNG.L (38 + u) == 37 + u &&
      HNG.R (38 + u) == letRk (FAData.g3Root.getD (u + 1) 0)

theorem root_ok : rootB = true := by quickRfl

theorem rowsA_eq : rowsA = rows5 (sg 0) := by
  rw [HNStrong.rowsA_eq]
  exact rows5_congr fun i hi => (Nat.eq_of_beq_eq_true (allN_spec tieA i hi)).symm

theorem rowsB_eq : rowsB = rows5 (sg 1) := by
  rw [HNStrong.rowsB_eq]
  exact rows5_congr fun i hi => (Nat.eq_of_beq_eq_true (allN_spec tieB i hi)).symm

theorem root_letters : ∀ l ∈ FAData.g3Root, l = 1 ∨ l = 2 := by decide

theorem root_eq : wordM (seedSel rowsA rowsB) FAData.g3Root = rows5 (sg 58) := by
  have hr := root_ok
  simp only [rootB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hr
  obtain ⟨⟨⟨hlen, h37o⟩, h37l⟩, hs⟩ := hr
  have hlt : ∀ l, letRk l < 86 := fun l => by unfold letRk; split <;> omega
  have e : (58 : Nat) = 36 + FAData.g3Root.length := by rw [hlen]
  rw [e]
  refine wordM5_chain (LT := fun l => sg (letRk l)) (Q := fun t => sg (36 + t)) (by rw [hlen]; omega)
    (fun l hl => ?_) (fun l _ => canon _ (hlt l)) (fun t _ ht => canon _ (by rw [hlen] at ht; omega))
    (fun i hi => (copyG (by omega) h37o h37l i hi).symm) (fun t h1 ht i hi => ?_)
  · rcases root_letters l hl with rfl | rfl
    · exact rowsA_eq
    · exact rowsB_eq
  · rw [hlen] at ht
    obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    obtain ⟨⟨a, b⟩, c⟩ := hs u (by omega)
    have := mulG (by omega) a b c i hi
    rwa [show 36 + (u + 1 + 1) = 38 + u by omega, show 36 + (u + 1) = 37 + u by omega]

@[expose] def letHk (l : Int) : Nat := if 0 < l then 2 + l.toNat else 19 + (-l).toNat

@[expose] noncomputable def hchk (w : List Int) (k : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun l t ih k => l != 0 && decide (l.natAbs ≤ 17) && decide (k < 86) && HNG.L k == letHk l &&
      bif t.isEmpty then HNG.OP k == 1 else HNG.OP k == 0 && HNG.R k == k - 1 && ih (k - 1)) w k

theorem hchk_nil (k : Nat) : hchk [] k = false := rfl

theorem hchk_cons (l : Int) (t : List Int) (k : Nat) : hchk (l :: t) k =
    (l != 0 && decide (l.natAbs ≤ 17) && decide (k < 86) && HNG.L k == letHk l &&
      bif t.isEmpty then HNG.OP k == 1 else HNG.OP k == 0 && HNG.R k == k - 1 && hchk t (k - 1)) :=
  rfl

theorem hword_ok : hchk FAData.g3H 71 = true := by quickRfl

theorem letHk_eq {l : Int} (h0 : l ≠ 0) (h17 : l.natAbs ≤ 17) :
    mletter HNStrong.SA HNStrong.SIA l = rows5 (sg (letHk l)) := by
  rw [HNStrong.mletter_eq h0 h17]
  refine rows5_congr fun i hi => ?_
  unfold HNStrong.letK letHk
  by_cases hp : 0 < l
  · rw [if_pos hp, if_pos hp]
    have h : Nat.beq (sg (3 + (l.toNat - 1)) i) (HNStrong.ss (13 + (l.toNat - 1)) i) = true :=
      allN_spec (allN_spec tieF (l.toNat - 1) (by omega)) i hi
    rw [show 3 + (l.toNat - 1) = 2 + l.toNat by omega,
      show 13 + (l.toNat - 1) = 12 + l.toNat by omega] at h
    exact (Nat.eq_of_beq_eq_true h).symm
  · rw [if_neg hp, if_neg hp]
    have h : Nat.beq (sg (20 + ((-l).toNat - 1)) i) (HNStrong.ss (30 + ((-l).toNat - 1)) i) =
        true := allN_spec (allN_spec tieFI ((-l).toNat - 1) (by omega)) i hi
    rw [show 20 + ((-l).toNat - 1) = 19 + (-l).toNat by omega,
      show 30 + ((-l).toNat - 1) = 29 + (-l).toNat by omega] at h
    exact (Nat.eq_of_beq_eq_true h).symm

theorem letHk_lt {l : Int} (h17 : l.natAbs ≤ 17) : letHk l < 86 := by
  unfold letHk
  split <;> omega

theorem mword_chain (w : List Int) (k : Nat) (h : hchk w k = true) :
    mword HNStrong.SA HNStrong.SIA w = rows5 (sg k) := by
  induction w generalizing k with
  | nil =>
    rw [hchk_nil] at h
    exact absurd h (by decide)
  | cons l t ih =>
    rw [hchk_cons] at h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨h0, h17⟩, hk⟩, hl⟩, hrest⟩ := h
    cases t with
    | nil =>
      simp only [List.isEmpty_nil, cond_true, beq_iff_eq] at hrest
      rw [mword, mword, letHk_eq h0 h17, mulM5_idR (canon _ (letHk_lt h17))]
      exact rows5_congr (copyG hk hrest hl)
    | cons a t' =>
      simp only [List.isEmpty_cons, cond_false, Bool.and_eq_true, beq_iff_eq] at hrest
      obtain ⟨⟨ho, hr⟩, hw⟩ := hrest
      rw [mword, letHk_eq h0 h17, ih (k - 1) hw]
      exact mul_eq (letHk_lt h17) (by omega) hk ho hl hr

theorem hword_eq : mword HNStrong.SA HNStrong.SIA FAData.g3H = rows5 (sg 71) :=
  mword_chain _ _ hword_ok

@[expose] noncomputable def powB : Bool :=
  HNG.OP 72 == 0 && HNG.L 72 == 58 && HNG.R 72 == 71 && HNG.OP 73 == 1 && HNG.L 73 == 72 &&
    HNG.OP 76 == 1 && HNG.L 76 == 75 &&
    (List.range 2).all (fun u => HNG.OP (74 + u) == 0 && HNG.L (74 + u) == 73 + u &&
      HNG.R (74 + u) == 72) &&
    (List.range 9).all fun u => HNG.OP (77 + u) == 0 && HNG.L (77 + u) == 76 + u &&
      HNG.R (77 + u) == 75

theorem pow_ok : powB = true := by quickRfl

theorem g3Mat_eq : g3Mat rowsA rowsB = rows5 (sg 72) := by
  have hp := pow_ok
  simp only [powB, Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨ho, hl⟩, hr⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hp
  unfold g3Mat
  dsimp only
  rw [HNStrong.strong_eq]
  dsimp only
  rw [root_eq, hword_eq]
  exact mul_eq (by omega) (by omega) (by omega) ho hl hr

theorem pow_g : powM 5 133 (rows5 (sg 72)) 3 = rows5 (sg 75) := by
  have hp := pow_ok
  simp only [powB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hp
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, h73o⟩, h73l⟩, -⟩, -⟩, hs⟩, -⟩ := hp
  refine powM5_chain (P := fun t => sg (72 + t)) (by omega) (canon _ (by omega))
    (fun t _ ht => canon _ (by omega)) (fun i hi => (copyG (by omega) h73o h73l i hi).symm) fun t h1 ht i hi => ?_
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  obtain ⟨⟨a, b⟩, c⟩ := hs u (by omega)
  have := mulG (by omega) a b c i hi
  rwa [show 72 + (u + 1 + 1) = 74 + u by omega, show 72 + (u + 1) = 73 + u by omega]

theorem pow_w {e : Nat} (h1 : 1 ≤ e) (he : e ≤ 10) :
    powM 5 133 (rows5 (sg 75)) e = rows5 (sg (75 + e)) := by
  have hp := pow_ok
  simp only [powB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hp
  obtain ⟨⟨⟨⟨-, h76o⟩, h76l⟩, -⟩, hs⟩ := hp
  refine powM5_chain (P := fun t => sg (75 + t)) h1 (canon _ (by omega))
    (fun t _ ht => canon _ (by omega)) (fun i hi => (copyG (by omega) h76o h76l i hi).symm) fun t h1 ht i hi => ?_
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  obtain ⟨⟨a, b⟩, c⟩ := hs u (by omega)
  have := mulG (by omega) a b c i hi
  rwa [show 75 + (u + 1 + 1) = 77 + u by omega, show 75 + (u + 1) = 76 + u by omega]

theorem g3_ok : g3OrderChecks rowsA rowsB = true := by
  unfold g3OrderChecks
  dsimp only
  rw [g3Mat_eq, pow_g, pow_w (e := 10) (by omega) (by omega), pow_w (e := 5) (by omega) (by omega),
    pow_w (e := 2) (by omega) (by omega)]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨by decide, by decide⟩, eqId5_sound fun i hi => ?_⟩, ?_⟩, ?_⟩
  · exact Nat.eq_of_beq_eq_true (allN_spec id85 i hi)
  · refine notId5_sound (canon _ (by omega)) ⟨0, by omega, fun h => ?_⟩
    have := ne80
    rw [h] at this
    simp at this
  · refine notId5_sound (canon _ (by omega)) ⟨0, by omega, fun h => ?_⟩
    have := ne77
    rw [h] at this
    simp at this

end CertificateChecks.KernelSporSch.HNG3

end
