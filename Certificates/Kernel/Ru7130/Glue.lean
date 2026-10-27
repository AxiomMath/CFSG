
module

public import Certificates.Kernel.Ru7130.Rep
public import Certificates.Kernel.Ru7130.Ker
public import Certificates.Kernel.Ru7130.Orb
public import CFSG.Certificates.Kernel.PcReachSound
public import CFSG.Quasithin.Background.A312SporRuBase
import all CFSG.Quasithin.Background.A312SporRuBase

set_option maxRecDepth 200000

public section

namespace CFSG.KD.Ru7130

open CFSG.KC.Enum CFSG.KS CFSG.KC.LQT.PcW CFSG.KC.HSA312 CFSG.KC.PcReach
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.RuCert CFSG.Quasithin.A312S CFSG.Quasithin.A312S.Ru
open CFSG.QuasithinUnique.Ch1.SporLat.Ru CFSG.QuasithinUnique.Vol2Native.A312L Matrix
open CFSG.Sporadic.Ru.Native (ruData)

abbrev GRu : Type := ↥(CFSG.Sporadic.SmallF2.J ruData)

theorem rep_eval {els : Array GRu} {L : Nat → Nat}
    (hL : ∀ l < els.size, Rep 4060 12 (L l) (tab ruData.n (els.getD l 1)).toArray) :
    ∀ w : List Nat, (∀ l ∈ w, l < els.size) →
      Rep 4060 12 (wordPB 4060 12 (mask 12) L w I) (tab ruData.n (evalElt els w)).toArray
  | [], _ => by
    rw [evalElt_nil, tab_one_toArray]
    exact hid
  | l :: w, h => by
    have e : wordPB 4060 12 (mask 12) L (l :: w) I =
        pcS 4060 12 (mask 12) (L l) (wordPB 4060 12 (mask 12) L w I) := rfl
    rw [e, evalElt_cons, tabArr_mul]
    exact rep_comp hn hw (hL l (h l (by simp))) (rep_eval hL w fun l' hl' => h l' (by simp [hl']))

theorem rep_pow' {c : Nat} {g : GRu} (h : Rep 4060 12 c (tab ruData.n g).toArray) (k : Nat) :
    Rep 4060 12 (powS 4060 12 (mask 12) I c k) (tab ruData.n (g ^ k)).toArray := by
  rw [tab_pow]
  exact rep_pow hn hw hid h k

theorem getD_map_toArray {α β : Type} {l : List α} (f : α → β) {i : Nat} (hi : i < l.length)
    (d : β) (d' : α) : (l.map f).toArray.getD i d = f (l.getD i d') := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, hi]

section Elts

noncomputable def Rl : List GRu := ruQuot2.map fun x => evalElt ruE2.toArray x.w ^ x.k

noncomputable def Cl : List GRu := ruKer.map fun c => evalElt Rl.toArray c.u ^ c.k

noncomputable def Hl : List GRu := J.hW.map fun v => evalElt Cl.toArray v

noncomputable def ruC : Subgroup GRu := Subgroup.closure {x | x ∈ Cl}

theorem hLE : ∀ l < ruE2.toArray.size,
    Rep 4060 12 (Lc l) (tab ruData.n (ruE2.toArray.getD l 1)).toArray := by
  intro l hl
  rw [← ruE2_hel l hl]
  have hl' : l < ruQuotL2.length := by rw [ruE2_size] at hl; rw [len2]; exact hl
  rw [getD_toArray hl']
  exact rL2 l hl'

theorem kLen : J.K.length = 8 := by decide +kernel

theorem kerLen : ruKer.length = 8 := rfl

theorem hR : ∀ i < Rl.toArray.size,
    Rep 4060 12 (R i) (tab ruData.n (Rl.toArray.getD i 1)).toArray := by
  intro i hi
  have hi' : i < ruQuot2.length := by simpa [Rl] using hi
  rw [Rl, getD_map_toArray _ hi' 1 default]
  have hw' : ∀ l ∈ (ruQuot2.getD i default).w, l < ruE2.toArray.size := by
    rw [ruE2_size]
    have : ∀ j < 2, ∀ l ∈ (ruQuot2.getD j default).w, l < 4 := by decide
    exact this i hi'
  have e := List.all_eq_true.1 rQ i (List.mem_range.2 hi')
  rw [← Nat.eq_of_beq_eq_true e]
  exact rep_pow' (rep_eval hLE _ hw') _

theorem hK : ∀ i < Cl.toArray.size,
    Rep 4060 12 (J.K.getD i 0) (tab ruData.n (Cl.toArray.getD i 1)).toArray := by
  intro i hi
  have hi' : i < ruKer.length := by simpa [Cl] using hi
  rw [Cl, getD_map_toArray _ hi' 1 default]
  have hw' : ∀ l ∈ (ruKer.getD i default).u, l < Rl.toArray.size := by
    have h2 : Rl.toArray.size = 2 := by simp [Rl]; rfl
    rw [h2]
    have : ∀ j < 8, ∀ l ∈ (ruKer.getD j default).u, l < 2 := by decide
    exact this i hi'
  have e := List.all_eq_true.1 kG i (List.mem_range.2 hi')
  rw [← Nat.eq_of_beq_eq_true e]
  exact rep_pow' (rep_eval hR _ hw') _

theorem hH : ∀ j < Hl.toArray.size,
    Rep 4060 12 (J.H.getD j 0) (tab ruData.n (Hl.toArray.getD j 1)).toArray := by
  intro j hj
  have hW' := hW
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hW'
  obtain ⟨-, hW2⟩ := hW'
  have hj' : j < J.hW.length := by simpa [Hl] using hj
  rw [Hl, getD_map_toArray _ hj' 1 []]
  obtain ⟨hl, he⟩ := hW2 j hj'
  have hl' : ∀ l ∈ J.hW.getD j [], l < Cl.toArray.size := by
    intro l hlm
    have := Nat.blt_eq.mp (hl l hlm)
    rw [kLen] at this
    simpa [Cl, kerLen] using this
  rw [← Nat.eq_of_beq_eq_true he]
  exact rep_eval hK _ hl'

theorem Cl_mem : ∀ l < Cl.toArray.size, Cl.toArray.getD l 1 ∈ ruC := fun l hl => by
  have := evalElt_getD_mem_closure Cl.toArray hl
  rwa [LatCtx.toList_toArray_set] at this

theorem Hl_mem : ∀ j < Hl.toArray.size, Hl.toArray.getD j 1 ∈ ruC := by
  intro j hj
  have hj' : j < J.hW.length := by simpa [Hl] using hj
  rw [Hl, getD_map_toArray _ hj' 1 []]
  have hW' := hW
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hW'
  refine evalElt_mem Cl.toArray Cl_mem _ fun l hlm => ?_
  have := Nat.blt_eq.mp ((hW'.2 j hj').1 l hlm)
  rw [kLen] at this
  simpa [Cl, kerLen] using this

theorem hm : mask 12 = 4095 := rfl

theorem nRu : ruData.n = 4060 := rfl

theorem n0 : 0 < ruData.n := by rw [nRu]; norm_num

theorem n2 : 2 < ruData.n := by rw [nRu]; norm_num

theorem act_code {c : Nat} {g : GRu} (h : Rep 4060 12 c (tab ruData.n g).toArray) {p : Nat}
    (hp : p < ruData.n) :
    pg 12 4095 c p = act ruData.n g p := by
  rw [← hm, ← img_rep h hp, img_tab]

theorem card_ge {Γ : Type} [Group Γ] {n : Nat} [MulAction Γ (Fin n)] [Finite Γ] (C : Subgroup Γ)
    {x y : Nat} (P Q : List Nat) (hP : P.Nodup) (hQ : Q.Nodup)
    (hPC : ∀ p ∈ P, ∃ g ∈ C, act n g x = p)
    (hQC : ∀ q ∈ Q, ∃ g ∈ C, act n g x = x ∧ act n g y = q) (hx : x < n) :
    P.length * Q.length ≤ Nat.card C := by
  choose a ha hax using fun i : Fin P.length => hPC P[i] (List.getElem_mem _)
  choose b hb hbx hby using fun j : Fin Q.length => hQC Q[j] (List.getElem_mem _)
  have hf : Function.Injective
      (fun ij : Fin P.length × Fin Q.length =>
        (⟨a ij.1 * b ij.2, C.mul_mem (ha _) (hb _)⟩ : C)) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h1 : a i * b j = a i' * b j' := Subtype.ext_iff.mp h
    have hii : i = i' := by
      have e := congrArg (fun g => act n g x) h1
      simp only [act_mul _ _ hx, hbx, hax] at e
      exact Fin.ext ((List.Nodup.getElem_inj_iff hP).mp e)
    subst hii
    have h2 : b j = b j' := mul_left_cancel h1
    have e := congrArg (fun g => act n g y) h2
    simp only [hby] at e
    exact Prod.ext rfl (Fin.ext ((List.Nodup.getElem_inj_iff hQ).mp e))
  have := Nat.card_le_card_of_injective _ hf
  simpa [Nat.card_prod] using this

theorem ruC_card : 2048 ≤ Nat.card ruC := by
  have hk := kOrb
  simp only [Bool.and_eq_true, beq_iff_eq] at hk
  have h1 := reachC_sound (P := fun q => ∃ g ∈ ruC, act ruData.n g 0 = q) (fun q i hq hi => by
      obtain ⟨g, hg, rfl⟩ := hq
      have hi' : i < Cl.toArray.size := by simpa [Cl, kLen, kerLen] using hi
      refine ⟨Cl.toArray.getD i 1 * g, ruC.mul_mem (Cl_mem i hi') hg, ?_⟩
      rw [act_code (hK i hi') (act_lt g n0), act_mul _ _ n0])
    J.O0 1 (fun q hq => ⟨1, ruC.one_mem, by
      rw [act_one n0]
      have : (2 ^ 0 : Nat).testBit q = true := hq
      rw [Nat.testBit_two_pow] at this
      exact of_decide_eq_true this⟩) hk.1
  have ho := hW
  simp only [Bool.and_eq_true, beq_iff_eq] at ho
  have hf := hFix
  have hh := hOrb
  simp only [Bool.and_eq_true, beq_iff_eq] at hh
  have hHlen : J.H.length = Hl.toArray.size := by simp [Hl, ho.1]
  have h2 := reachC_sound
    (P := fun q => ∃ g ∈ ruC, act ruData.n g 0 = 0 ∧ act ruData.n g 2 = q) (fun q j hq hj => by
      obtain ⟨g, hg, hg0, rfl⟩ := hq
      have hj' : j < Hl.toArray.size := by rw [← hHlen]; exact hj
      have hfix : act ruData.n (Hl.toArray.getD j 1) 0 = 0 := by
        rw [← act_code (hH j hj') n0]
        have hmem : J.H.getD j 0 ∈ J.H := by
          rw [List.getD_eq_getElem _ _ hj]
          exact List.getElem_mem hj
        exact beq_iff_eq.mp (List.all_eq_true.1 hf _ hmem)
      refine ⟨Hl.toArray.getD j 1 * g, ruC.mul_mem (Hl_mem j hj') hg, ?_, ?_⟩
      · rw [act_mul _ _ n0, hg0, hfix]
      · rw [act_code (hH j hj') (act_lt g n2), act_mul _ _ n2])
    J.O1 4 (fun q hq => ⟨1, ruC.one_mem, act_one n0, by
      rw [act_one n2]
      have : (2 ^ 2 : Nat).testBit q = true := hq
      rw [Nat.testBit_two_pow] at this
      exact of_decide_eq_true this⟩) hh.1
  have hP : (0 :: J.O0.map fun r => Nat.land r 4095).Nodup := by
    refine List.nodup_cons.mpr ⟨fun hm => ?_, h1.1⟩
    exact absurd (h1.2 0 hm).1 (by decide)
  have hQ : (2 :: J.O1.map fun r => Nat.land r 4095).Nodup := by
    refine List.nodup_cons.mpr ⟨fun hm => ?_, h2.1⟩
    exact absurd (h2.2 2 hm).1 (by decide)
  have := card_ge ruC _ _ hP hQ (fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨1, ruC.one_mem, act_one n0⟩
      · exact (h1.2 p hp).2) (fun q hq => by
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨1, ruC.one_mem, act_one n0, act_one n2⟩
      · exact (h2.2 q hq).2) n0
  simp only [List.length_cons, List.length_map, hk.2, hh.2] at this
  exact this

theorem mem_getD {α : Type} {l : List α} {y : α} (d : α) (hy : y ∈ l) :
    ∃ i < l.toArray.size, l.toArray.getD i d = y := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  exact ⟨i, by simpa using hi, by simp [Array.getD_eq_getD_getElem?, hi]⟩

theorem ruB_eq : ruB = [0, 1, 2, 3, 4] := by decide +kernel

theorem Rl_odd : ∀ x ∈ Rl, ∃ m, m % 2 = 1 ∧ x ^ m = 1 := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := mem_getD 1 hx
  have hi' : i < ruQuot2.length := by simpa [Rl] using hi
  refine ⟨(ruQuot2.getD i default).m, ?_, ?_⟩
  · have : ∀ j < 2, (ruQuot2.getD j default).m % 2 = 1 := by decide
    exact this i hi'
  · apply base_property ru_facts
    intro b hb
    have hb' : b ∈ [0, 1, 2, 3, 4] := by rw [← ruB_eq]; exact hb
    have hbn : b < ruData.n := base_lt ru_facts b hb
    rw [← act_code (rep_pow' (hR i hi) _) hbn]
    have e := List.all_eq_true.1 rOrd i (List.mem_range.2 hi')
    exact beq_iff_eq.mp (List.all_eq_true.1 e b hb')

theorem Rl_mem : ∀ x ∈ Rl, x ∈ ruCtx.Y 2 := by
  have hels : ∀ l < ruE2.toArray.size, ruE2.toArray.getD l 1 ∈ ruCtx.Y 2 := fun l hl =>
    ruLetter_mem (by rw [ruE2_size] at hl; exact hl)
  have hw : ∀ q ∈ ruQuot2, ∀ l ∈ q.w, l < ruE2.toArray.size := by
    rw [ruE2_size]
    decide
  intro x hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
  exact Subgroup.pow_mem _ (evalElt_mem ruE2.toArray hels q.w (hw q hq)) _

theorem ruC_le : ruC ≤ Subgroup.closure {x | x ∈ Rl} := by
  rw [ruC, Subgroup.closure_le]
  intro y hy
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
  have hels : ∀ l < Rl.toArray.size, Rl.toArray.getD l 1 ∈ Subgroup.closure {y | y ∈ Rl} :=
    fun l hl => by
      have := evalElt_getD_mem_closure Rl.toArray hl
      rwa [LatCtx.toList_toArray_set] at this
  have hu : ∀ c ∈ ruKer, ∀ l ∈ c.u, l < Rl.toArray.size := by
    have h2 : Rl.toArray.size = 2 := by simp [Rl]; rfl
    rw [h2]
    decide
  exact Subgroup.pow_mem _ (evalElt_mem Rl.toArray hels c.u (hu c hc)) _

theorem Cl_comm : ∀ l < Cl.toArray.size, ∀ i,
    Cl.toArray.getD l 1 * ruV i = ruV i * Cl.toArray.getD l 1 := by
  intro l hl i
  apply eq_of_tabArr_eq (base_lt ru_facts) (base_property ru_facts)
  rw [tabArr_mul, tabArr_mul, ru_hv i]
  have hiV : (i : Nat) < Vs.length := by simp [Vs, ruVWords]
  have hV := rV.2 i hiV
  have e : ruVTabs.toList.getD i #[] = ruVTabs.getD i #[] := by
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  rw [e] at hV
  have hl8 : l < J.K.length := by
    rw [kLen]
    simpa [Cl, kerLen] using hl
  have hk : J.K.getD l 0 ∈ J.K := by
    rw [List.getD_eq_getElem _ _ hl8]
    exact List.getElem_mem hl8
  have hv : Vs.getD i 0 ∈ Vs := by
    rw [List.getD_eq_getElem _ _ hiV]
    exact List.getElem_mem hiV
  exact comp_eq hn hw (hK l hl) hV hV (hK l hl)
    (List.all_eq_true.1 (List.all_eq_true.1 kV _ hk) _ hv)

theorem ruC_comm : ∀ y ∈ ruC, ∀ i, Commute y (ruV i) := by
  intro y hy i
  have hle : ruC ≤ Subgroup.centralizer {ruV i} := by
    rw [ruC, Subgroup.closure_le]
    intro z hz
    obtain ⟨l, hl, rfl⟩ := mem_getD 1 hz
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    first
    | exact Cl_comm l hl i
    | exact (Cl_comm l hl i).symm
  have h := Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  first
  | exact h
  | exact h.symm

end Elts

section Psi

theorem ruE8K : E8Basis ruV ∧ ∀ l < ruQuotL2.toArray.size, ∀ i : Fin 3,
    ruLetter l * ruV i * (ruLetter l)⁻¹ = e8Elt ruV fun r => ruMat l r i := by
  refine e8_of_check (B := ruB) (base_lt ru_facts) (base_property ru_facts) ru_hv
    (fun l hl => ?_) ru_hM e8Check_ru
  rw [ruLetter, ruE2_hel l (by rw [ruE2_size]; exact ruQuotL2_size ▸ hl)]

theorem normK : ruCtx.Y 2 ≤ e8Norm ruE8K.1 := by
  rw [LatCtx.Y, Subgroup.closure_le]
  intro x hx
  have hx' : x ∈ ruE2 := hx
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hx'
  have hl4 : l < 4 := by
    have := ruE2_size
    rw [List.size_toArray] at this
    omega
  have hlet : ruE2[l] = ruLetter l := by
    rw [ruLetter, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_eq_getElem hl]
    rfl
  have hm := mem_e8Norm ruE8K.1 (ruMat l) (ruE8K.2 l (by rw [ruQuotL2_size]; exact hl4))
  rw [← hlet] at hm
  exact hm

noncomputable def psiK : ↥(ruCtx.Y 2) →* SpecialLinearGroup (Fin 3) (ZMod 2) :=
  (e8SL ruE8K.1).comp (Subgroup.inclusion normK)

theorem psiK_letter {l : ℕ} (hl : l < 4) : psiK ⟨ruLetter l, ruLetter_mem hl⟩ = ruSL l :=
  e8SL_eq ruE8K.1 _ (ruSL l) (ruE8K.2 l (by rw [ruQuotL2_size]; exact hl))

theorem psiK_surjective : Function.Surjective psiK := by
  have h3 : ruSL 3 ∈ psiK.range := ⟨_, psiK_letter (l := 3) (by norm_num)⟩
  have h4 : ruSL 1 * ruSL 2 ∈ psiK.range :=
    ⟨⟨ruLetter 1, ruLetter_mem (by norm_num)⟩ * ⟨ruLetter 2, ruLetter_mem (by norm_num)⟩, by
      rw [map_mul, psiK_letter (l := 1) (by norm_num), psiK_letter (l := 2) (by norm_num)]⟩
  have h7 : ruSL 2 * ruSL 3 ∈ psiK.range :=
    ⟨⟨ruLetter 2, ruLetter_mem (by norm_num)⟩ * ⟨ruLetter 3, ruLetter_mem (by norm_num)⟩, by
      rw [map_mul, psiK_letter (l := 2) (by norm_num), psiK_letter (l := 3) (by norm_num)]⟩
  have o3 : orderOf (ruSL 3) = 3 := by
    apply orderOf_eq_prime (hp := ⟨Nat.prime_three⟩)
    · exact Subtype.ext (show ruMat 3 ^ 3 = 1 by decide +kernel)
    · intro h
      have h' : ruMat 3 = 1 := congrArg Subtype.val h
      revert h'
      decide +kernel
  have o4 : orderOf (ruSL 1 * ruSL 2) = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := ruSL 1 * ruSL 2)
      (hp := ⟨Nat.prime_two⟩) ?_ ?_
    · rw [h]
      norm_num
    · intro h
      have h' : (ruMat 1 * ruMat 2) ^ 2 ^ 1 = 1 := congrArg Subtype.val h
      revert h'
      decide +kernel
    · exact Subtype.ext (show (ruMat 1 * ruMat 2) ^ 2 ^ (1 + 1) = 1 by decide +kernel)
  have o7 : orderOf (ruSL 2 * ruSL 3) = 7 := by
    apply orderOf_eq_prime (hp := ⟨by norm_num⟩)
    · exact Subtype.ext (show (ruMat 2 * ruMat 3) ^ 7 = 1 by decide +kernel)
    · intro h
      have h' : ruMat 2 * ruMat 3 = 1 := congrArg Subtype.val h
      revert h'
      decide +kernel
  exact MonoidHom.range_eq_top.mp (eq_top_of_orders_sl32 h3 h4 h7 o3 o4 o7)

theorem psiK_ker_card : Nat.card psiK.ker = 2048 := by
  have h1 := card_eq_card_ker_mul_card_range psiK
  rw [MonoidHom.range_eq_top.mpr psiK_surjective, Subgroup.card_top,
    CFSG.QuasithinUnique.Vol2Native.A312L.Seven.card_slThree, ru_member_card 2 (by norm_num)] at h1
  have h2 : (#[1, 15, 21, 3, 3] : Array ℕ)[2]! * 16384 = 2048 * 168 := rfl
  rw [h2] at h1
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h1).symm

theorem quot2K (N : Subgroup (ruCtx.Y 2)) [N.Normal] (hp : IsPGroup 2 (ruCtx.Y 2 ⧸ N)) :
    Nat.card (ruCtx.Y 2 ⧸ N) ≤ 1 :=
  quot_le_one_of_ker_le psiK psiK_surjective N hp
    (ker_le_of_odd_closure psiK Rl_mem Rl_odd ruC_le
      (fun x _ hxC => e8SL_eq_one ruE8K.1 _ (ruC_comm x hxC))
      (by rw [psiK_ker_card]; exact ruC_card) N hp)

theorem ru7130 :
    (∃ ψ : ↥(ruCtx.Y 2) →* SpecialLinearGroup (Fin 3) (ZMod 2), Function.Surjective ψ) ∧
      ∀ (N : Subgroup ↥(ruCtx.Y 2)) [N.Normal], IsPGroup 2 (↥(ruCtx.Y 2) ⧸ N) →
        Nat.card (↥(ruCtx.Y 2) ⧸ N) ≤ 1 :=
  ⟨⟨psiK, psiK_surjective⟩, fun N _ hp => quot2K N hp⟩

end Psi

end CFSG.KD.Ru7130

end
