
module

public import Certificates.Kernel.SchreierFam.C22241K
public import CFSG.Certificates.Kernel.BfsPairsSound
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1UBridgeBase
public import Certificates.Data.CatFactsL4U4P1U43Data

public section

namespace CertificateChecks.KernelSchreierFam.C22241

open CFSG.KC.BfsPairs CFSG.LieType.Multipliers.U43 CFSG.ComponentClassification.HarrisLit.P1
  CFSG.ComponentClassification.HarrisLit.P1.U43 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native Matrix
  CFSG.Assembly.LowTwoRank

theorem ap_tu {k j : ℕ} (hj : j < 820) :
    ap (tu k false) j = ptIndex (mv4 (matN9 k) (decode j)) := by
  rw [tu, ap_ofFn _ hj, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (ptIndex_lt_two_pow _)]
  rfl

theorem good_tu {b c₁ c₂ : ℕ} (hb : b < 820)
    (u₁ : ((matN9 c₁).map (· ^ 3))ᵀ * matN9 c₁ = 1) (d₁ : (matN9 c₁).det = 1)
    (u₂ : ((matN9 c₂).map (· ^ 3))ᵀ * matN9 c₂ = 1) (d₂ : (matN9 c₂).det = 1)
    (f₁ : ptIndex (mv4 (matN9 c₁) (decode b)) = b) (f₂ : ptIndex (mv4 (matN9 c₂) (decode b)) = b)
    (ho : onlyFix b c₁ c₂ = true) :
    Good 820 psi.range b (tu c₁ false, tu c₂ false) := by
  let A₁ : StatedSU 4 3 F9 := ⟨GeneralLinearGroup.mk'' (matN9 c₁) (by rw [d₁]; exact isUnit_one),
    Subgroup.subset_closure ⟨d₁, u₁⟩⟩
  let A₂ : StatedSU 4 3 F9 := ⟨GeneralLinearGroup.mk'' (matN9 c₂) (by rw [d₂]; exact isUnit_one),
    Subgroup.subset_closure ⟨d₂, u₂⟩⟩
  have r₁ : Rep 820 (tu c₁ false) (psi (QuotientGroup.mk A₁)) := by
    rw [psi_mk]
    exact rep_tu_false rfl
  have r₂ : Rep 820 (tu c₂ false) (psi (QuotientGroup.mk A₂)) := by
    rw [psi_mk]
    exact rep_tu_false rfl
  have e₁ : ∀ j < 820, idx 820 (psi (QuotientGroup.mk A₁)) j =
      ptIndex (mv4 (matN9 c₁) (decode j)) := fun j hj => (r₁ j hj).symm.trans (ap_tu hj)
  have e₂ : ∀ j < 820, idx 820 (psi (QuotientGroup.mk A₂)) j =
      ptIndex (mv4 (matN9 c₂) (decode j)) := fun j hj => (r₂ j hj).symm.trans (ap_tu hj)
  have m₁ : psi (QuotientGroup.mk A₁) ∈ psi.range := MonoidHom.mem_range.2 ⟨_, rfl⟩
  have m₂ : psi (QuotientGroup.mk A₂) ∈ psi.range := MonoidHom.mem_range.2 ⟨_, rfl⟩
  have i₁ : idx 820 (psi (QuotientGroup.mk A₁)) b = b := by rw [e₁ b hb, f₁]
  have i₂ : idx 820 (psi (QuotientGroup.mk A₂)) b = b := by rw [e₂ b hb, f₂]
  unfold Good
  dsimp only
  refine ⟨hb, _, m₁, _, m₂, r₁, r₂, i₁, i₂, ?_⟩
  intro j hj h₁ h₂
  rw [e₁ j hj] at h₁
  rw [e₂ j hj] at h₂
  have h := List.all_eq_true.1 ho j (List.mem_range.2 hj)
  simpa [h₁, h₂] using h

theorem pair_mul_uncode (r s d : ℕ) : (⟨(r : ZMod 3), (s : ZMod 3)⟩ : F9) * uncode d =
    ⟨((r * (d / 3) + 2 * s * (d % 3) : ℕ) : ZMod 3),
      ((r * (d % 3) + s * (d / 3) : ℕ) : ZMod 3)⟩ := by
  have key : ∀ x y z u : ZMod 3, x * y - z * u = x * y + 2 * z * u := by decide
  apply F9.ext
  · change (r : ZMod 3) * ((d / 3 : ℕ) : ZMod 3) - (s : ZMod 3) * ((d % 3 : ℕ) : ZMod 3) = _
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    exact key _ _ _ _
  · change (r : ZMod 3) * ((d % 3 : ℕ) : ZMod 3) + (s : ZMod 3) * ((d / 3 : ℕ) : ZMod 3) = _
    simp only [Nat.cast_add, Nat.cast_mul]

theorem add4_pair (x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℕ) :
    (⟨(x₀ : ZMod 3), (y₀ : ZMod 3)⟩ : F9) + ⟨x₁, y₁⟩ + ⟨x₂, y₂⟩ + ⟨x₃, y₃⟩ =
      ⟨((x₀ + x₁ + x₂ + x₃ : ℕ) : ZMod 3), ((y₀ + y₁ + y₂ + y₃ : ℕ) : ZMod 3)⟩ := by
  apply F9.ext
  · change (x₀ : ZMod 3) + x₁ + x₂ + x₃ = _
    simp only [Nat.cast_add]
  · change (y₀ : ZMod 3) + y₁ + y₂ + y₃ = _
    simp only [Nat.cast_add]

theorem decode_eq_u43DCode (j : ℕ) (i : Fin 4) : decode j i = uncode (u43DCode j i) := by
  have h3 : uncode 3 = 1 := by decide
  have h0 : uncode 0 = 0 := by decide
  fin_cases i <;> simp [decode, u43DCode] <;> split_ifs <;> simp_all

theorem u43DCode_u43Lead (j : ℕ) : u43DCode j (u43Lead j) = 3 := by
  unfold u43DCode u43Lead
  split_ifs <;> simp_all

theorem u43Lead_lt (j : ℕ) : u43Lead j < 4 := by
  unfold u43Lead
  split_ifs <;> omega

theorem mv4_eq_w (k j : ℕ) (i : Fin 4) :
    mv4 (matN9 k) (decode j) i = ⟨((wRe k j i : ℕ) : ZMod 3), ((wIm k j i : ℕ) : ZMod 3)⟩ := by
  have e : ∀ l : Fin 4, matN9 k i l * decode j l =
      ⟨((prRe (u43MCode k i l) (u43DCode j l) : ℕ) : ZMod 3),
        ((prIm (u43MCode k i l) (u43DCode j l) : ℕ) : ZMod 3)⟩ := fun l => by
    rw [decode_eq_u43DCode]
    exact pair_mul_uncode _ _ _
  simp only [mv4, e]
  rw [add4_pair]
  rfl

theorem eq_smul_decode {w : V} {j : ℕ} (h : ptIndex w = j) : ∃ t : F9, w = t • decode j := by
  by_cases hw : w = 0
  · exact ⟨0, by rw [hw, zero_smul]⟩
  have hj : j < 820 := by
    rw [← h]
    exact ptIndex_lt w
  have hd : ptIndex (decode j) = j := ptIndex_decode ⟨j, hj⟩
  have e : ptEquiv (Projectivization.mk F9 w hw) =
      ptEquiv (Projectivization.mk F9 (decode j) (decode_ne_zero j)) := by
    have m : (⟨ptIndex w, ptIndex_lt _⟩ : Fin 820) = ⟨ptIndex (decode j), ptIndex_lt _⟩ := by
      rw [Fin.mk.injEq]
      exact h.trans hd.symm
    exact ((ptEquiv_apply _).trans (ptFin_mk w hw)).trans
      (m.trans ((ptEquiv_apply _).trans (ptFin_mk _ (decode_ne_zero j))).symm)
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff _ _ _ _ _).1 (ptEquiv.injective e)
  exact ⟨a, by rw [← ha, Units.smul_def]⟩

theorem u43Fix_of {k j : ℕ} (h : ptIndex (mv4 (matN9 k) (decode j)) = j) : u43Fix k j = true := by
  obtain ⟨t, ht⟩ := eq_smul_decode h
  have hc : ∀ i : Fin 4, mv4 (matN9 k) (decode j) i = t * decode j i := fun i => by
    rw [ht, Pi.smul_apply, smul_eq_mul]
  have tp : t = ⟨((wRe k j (u43Lead j) : ℕ) : ZMod 3), ((wIm k j (u43Lead j) : ℕ) : ZMod 3)⟩ := by
    have := hc ⟨u43Lead j, u43Lead_lt j⟩
    rw [mv4_eq_w, decode_eq_u43DCode] at this
    change _ = t * uncode (u43DCode j (u43Lead j)) at this
    have u3 : uncode 3 = 1 := by decide
    rw [u43DCode_u43Lead, u3, mul_one] at this
    exact this.symm
  have f : ∀ i : Fin 4, u43FixAt k j i = true := fun i => by
    have := hc i
    rw [mv4_eq_w, decode_eq_u43DCode, tp, pair_mul_uncode] at this
    obtain ⟨h1, h2⟩ := F9.mk.inj this
    rw [ZMod.natCast_eq_natCast_iff'] at h1 h2
    simp only [u43FixAt, Bool.and_eq_true, beq_iff_eq]
    exact ⟨h1, h2⟩
  simp only [u43Fix, Bool.and_eq_true]
  exact ⟨⟨⟨f 0, f 1⟩, f 2⟩, f 3⟩

theorem onlyFix_of_N {b c₁ c₂ : ℕ} (h : onlyFixN b c₁ c₂ = true) : onlyFix b c₁ c₂ = true := by
  rw [onlyFix, List.all_eq_true]
  intro j hj
  have hj' := List.all_eq_true.1 h j hj
  by_cases e1 : ptIndex (mv4 (matN9 c₁) (decode j)) = j
  · by_cases e2 : ptIndex (mv4 (matN9 c₂) (decode j)) = j
    · rw [u43Fix_of e1, u43Fix_of e2] at hj'
      rw [e1, e2]
      simpa using hj'
    · simp [e2]
  · simp [e1]

theorem only0 : onlyFix 0 404334890521881 1352341616652227 = true := onlyFix_of_N only0N

theorem only4 : onlyFix 4 1309751274598484 1681408017212684 = true := onlyFix_of_N only4N

theorem stepU_eq : ∀ l < uPg.size, ∀ p < 820, stepU l p = ap uPg[l]! p := by
  intro l hl p hp
  have hl2 : l < 2 := hl
  interval_cases l
  · rw [uPg_zero, toTable, ap_ofFn _ hp, stepU, ite_eq_left rfl]
  · rw [uPg_one, toTable, ap_ofFn _ hp, stepU, ite_eq_right (by norm_num)]

theorem bases_good : ∀ b ∈ u43Bases, Good 820 psi.range b.1 b.2 := by
  intro b hb
  simp only [u43Bases, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl
  · exact good_tu (by norm_num) unitary1 det1 unitary2 det2 fixes.1 fixes.2.1 only0
  · exact good_tu (by norm_num) unitary3 det3 unitary4 det4 fixes.2.2.1 fixes.2.2.2 only4

theorem stepU_pk : stepU = stepPk := by
  have key : ∀ (t : Array ℕ) (P p : ℕ), pk10OK t.toList P = true →
      (UInt32.ofNat t[p]!).toNat = P / 1024 ^ p % 1024 := by
    intro t P p h
    have e : t[p]! = t.toList.getD p 0 := by
      rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, getElem!_def]
      cases t[p]? <;> rfl
    rw [UInt32.toNat_ofNat', e, pk10OK_getD _ P p h]
    exact Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num))
  funext l p
  rw [stepU, stepPk]
  split_ifs
  · exact key _ _ p pkA_ok
  · exact key _ _ p pkB_ok

theorem reach : (bfsReach 820 2 stepU [0, 4]).toList.all id = true := by
  have h : bfsReachF 820 32 2 stepU [0, 4] = 2 ^ 820 - 1 := by
    rw [stepU_pk]
    exact reachBits
  exact bfsReach_of_F (w := 32) (fun _ _ => UInt32.toNat_lt _) (by decide) h

theorem centTriv : centTrivOK 820 uSift u43CentTriv = true := by
  rw [u43CentTriv_def]
  exact centTrivOK_bfsPairs u43_groupData stepU_eq bases_good reach

end CertificateChecks.KernelSchreierFam.C22241
