module

public import Certificates.Kernel.ONKLat.Code
public import Certificates.Kernel.ONKLat.Checks
public import Certificates.Kernel.Sporadic.ON5.Final
public import CFSG.Sporadic.Schreier.ONIntersection

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONKL

open Equiv CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.ONSchreier
  CFSG.ONSchreier.Native CFSG.KC.Misc.ClosW CFSG.ComponentClassification.PSL3Four
  CertificateChecks.KernelSpor CertificateChecks.KernelSpor.ON5K Subgroup

theorem cent_pow_eq {G : Type*} [Group G] [Finite G] {y : G} {r k : ℕ} (hr : r.Prime)
    (hy : orderOf y = r) (hk0 : 0 < k) (hkr : k < r) : centralizer {y ^ k} = centralizer {y} := by
  have hc : Nat.Coprime r k :=
    (Nat.Prime.coprime_iff_not_dvd hr).2 fun h => absurd (Nat.le_of_dvd hk0 h) (by omega)
  have ho : orderOf (y ^ k) = r := by
    rw [orderOf_pow' y (by omega), hy, Nat.Coprime.gcd_eq_one hc, Nat.div_one]
  have hz : zpowers (y ^ k) = zpowers y :=
    Subgroup.eq_of_le_of_card_ge (zpowers_le.2 (pow_mem (mem_zpowers y) k))
      (by rw [Nat.card_zpowers, Nat.card_zpowers, ho, hy])
  have hm : y ∈ zpowers (y ^ k) := by
    rw [hz]
    exact mem_zpowers y
  obtain ⟨m, e⟩ := mem_zpowers_iff.1 hm
  ext g
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : Commute (y ^ k) g := h.symm
    have := (h'.zpow_left m).symm
    rw [e] at this
    exact this.eq
  · intro h
    have h' : Commute y g := h.symm
    exact ((h'.pow_left k).symm).eq

theorem rec_get120 {cnt i : ℕ} {T PL : ℕ → ℕ} (hi : i < cnt) :
    (penumRec 120 7 cnt T PL).tabs[i]! = unpack 120 7 (T i) := by
  rw [getElem!_pos _ i (by simp [penumRec, hi])]
  simp [penumRec]

theorem m120_eq : m120Enum = penumRec 120 7 ON5M.cnt ON5M.T ON5M.PL := m120_sound.1

theorem m120_size : m120Enum.tabs.size = 40320 := by
  rw [m120_eq]
  simp [penumRec]
  rfl

theorem code_M {k : ℕ}
    (hk : k < 40320) : ∃ g ∈ onM120Chain.originalSubgroup, wcode 7 g = ON5M.T k ∧
      TabRep (unpack 120 7 (ON5M.T k)) g := by
  have hs : k < m120Enum.tabs.size := by rw [m120_size]; exact hk
  obtain ⟨g, hg, hr⟩ := m120_enumerates.exists_elt hs
  have hc : k < ON5M.cnt := hk
  rw [m120_eq, rec_get120 hc] at hr
  exact ⟨g, hg, wcode_of_tab (by norm_num) (shr_of_canon (penumPt_canon (m_pt hc))) hr, hr⟩

theorem powP_zero (n w y : ℕ) : powP n w y 0 = pidn n w := rfl

theorem powP_succ (n w y k : ℕ) : powP n w y (k + 1) = pcomp n w (mask w) y (powP n w y k) := rfl

theorem wcode_powP_gen {n w : ℕ}
    (he : CFSG.KC.Misc.Clos.ClosEnc (wcode (n := n) w) (pcomp n w (mask w)) (pidn n w))
    (g : Perm (Fin n)) : ∀ k : ℕ, wcode w (g ^ k) = powP n w (wcode w g) k
  | 0 => by
    rw [pow_zero, powP_zero]
    exact he.enc_one
  | k + 1 => by
    rw [pow_succ', he.enc_mul, wcode_powP_gen he g k, powP_succ]

theorem wcode_powP (g : Perm (Fin 120)) (k : ℕ) : wcode 7 (g ^ k) = powP 120 7 (wcode 7 g) k :=
  wcode_powP_gen henc120 g k

theorem commF_iff_gen {n w : ℕ} (hn : 0 < n) (hw : n + 1 < 2 ^ w) (h32 : n < 2 ^ 32)
    (he : CFSG.KC.Misc.Clos.ClosEnc (wcode (n := n) w) (pcomp n w (mask w)) (pidn n w))
    {y g : Perm (Fin n)} : commF n w (wcode w y) (wcode w g) = true ↔ g * y = y * g := by
  unfold commF
  have key : ∀ a b : Perm (Fin n), pg w (mask w) (wcode w a) (pg w (mask w) (wcode w b) 0) =
      pg w (mask w) (wcode w (a * b)) 0 := fun a b => by
    rw [he.enc_mul]
    exact (PF.pg_pcomp h32 hn).symm
  rw [key g y, key y g]
  cases h1 : Nat.beq (pg w (mask w) (wcode w (g * y)) 0) (pg w (mask w) (wcode w (y * g)) 0)
  · refine ⟨fun h => (Bool.false_ne_true h).elim, fun h => ?_⟩
    rw [h, Nat.beq_refl] at h1
    exact Bool.noConfusion h1
  · have e : (Nat.beq (pcomp n w (mask w) (wcode w g) (wcode w y))
        (pcomp n w (mask w) (wcode w y) (wcode w g)) = true ↔ g * y = y * g) := by
      rw [← he.enc_mul, ← he.enc_mul, beq_code he]
    exact e

theorem commF_iff {y g : Perm (Fin 120)} :
    commF 120 7 (wcode 7 y) (wcode 7 g) = true ↔ g * y = y * g :=
  commF_iff_gen (by norm_num) (by norm_num) (by norm_num) henc120

theorem y_facts {r Y p : ℕ}
    {c : List ℕ} (hr : r.Prime) (hy : yOK r Y p = true) (hp : p < 40320)
    (hsel : ∀ s < 20, cS Y c s = true) (hlen : ((List.range 20).flatMap (slIn c)).length = r) :
    ∃ y ∈ onM120Chain.originalSubgroup, orderOf y = r ∧ ∀ k : ℕ, 0 < k → k < r →
      Nat.card ↥(centralizer {y ^ k} ⊓ onM120Chain.originalSubgroup) = r := by
  have : Fact r.Prime := ⟨hr⟩
  unfold yOK at hy
  simp only [bAnd_iff] at hy
  obtain ⟨hy1, hy2, hy3⟩ := hy
  obtain ⟨y, hyR, hyc, -⟩ := code_M hp
  rw [Nat.eq_of_beq_eq_true hy1] at hyc
  have hyr : y ^ r = 1 := by
    apply henc120.inj
    rw [wcode_powP, hyc, henc120.enc_one]
    exact Nat.eq_of_beq_eq_true hy2
  have hy1' : y ≠ 1 := fun h => by
    cases hb : Nat.beq Y (pidn 120 7)
    · have hY : Y = pidn 120 7 := by
        rw [← hyc, h]
        exact henc120.enc_one
      exact Nat.ne_of_beq_eq_false hb hY
    · rw [hb] at hy3
      exact Bool.false_ne_true hy3
  refine ⟨y, hyR, orderOf_eq_prime hyr hy1', fun k hk0 hkr => ?_⟩
  rw [cent_pow_eq hr (orderOf_eq_prime hyr hy1') hk0 hkr]
  have hE := m120_enumerates
  have hF := hE.filter (K := centralizer {y}) (fun t => commF 120 7 Y (tcode 120 7 t))
    (fun t g hg => by
      rw [← wcode_eq_tcode (fun i => hg.2 i), ← hyc, commF_iff, mem_centralizer_singleton_iff])
  rw [hF.card, ← Array.toList_filter, Array.length_toList, m120_eq]
  simp only [penumRec]
  rw [filter_ofFn (m := ON5M.cnt) (f := fun i => unpack 120 7 (ON5M.T i)), List.size_toArray,
    List.length_map]
  have hcnt : ON5M.cnt = 2016 * 20 := rfl
  have e : ((List.range ON5M.cnt).filter fun i =>
      commF 120 7 Y (tcode 120 7 (unpack 120 7 (ON5M.T i)))) = (List.range ON5M.cnt).filter (qC Y) := by
    apply List.filter_congr
    intro i hi
    have hi' : i < 40320 := List.mem_range.1 hi
    obtain ⟨g, -, hgc, hgr⟩ := code_M hi'
    rw [← wcode_eq_tcode (fun x => hgr.2 x), hgc]
    unfold qC
    rw [strictB_app']
  rw [e, hcnt, blocks_eq (qC Y) 2016 (slIn c) 20 fun s hs => by
    have h := selFrom_spec (qC Y) 2016 _ _ (hsel s hs)
    have e2 : Nat.mul s 2016 = 2016 * s := Nat.mul_comm s 2016
    rw [e2] at h
    exact h]
  exact hlen

theorem c5_len : ((List.range 20).flatMap (slIn c5)).length = 5 := by decide +kernel

theorem c7_len : ((List.range 20).flatMap (slIn c7)).length = 7 := by decide +kernel

theorem yPos_lt : List.getD yPos 0 0 < 40320 ∧ List.getD yPos 1 0 < 40320 := by decide +kernel

theorem exists_y :
    ∀ r : ℕ, r = 5 ∨ r = 7 → ∃ y ∈ onM120Chain.originalSubgroup, orderOf y = r ∧
      ∀ k : ℕ, 0 < k → k < r →
        Nat.card ↥(centralizer {y ^ k} ⊓ onM120Chain.originalSubgroup) = r := by
  rintro r (rfl | rfl)
  · exact y_facts (by norm_num) ch812105_y5 yPos_lt.1 c5All c5_len
  · exact y_facts (by norm_num) ch812105_y7 yPos_lt.2 c7All c7_len

end CertificateChecks.KernelSpor.ONKL

end
