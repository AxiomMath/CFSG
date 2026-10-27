
module

public import Certificates.Kernel.OmegaEight.SB3873GU
public import Certificates.Kernel.OmegaEight.FHom
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchNfHom
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSAut

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3873

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8 CFSG.KC.SBCen CFSG.KC.SBCenF
  CFSG.KC.SBCenL CFSG.KC.SBCenU CertificateChecks.KernelO8.FHom

@[expose] def gensLit : Nat := 11847271551353678797772040348580548905795587

@[expose] noncomputable def wpK (mul : Nat → Nat → Nat) (m : Nat) (ys : Nat → Nat) (e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun l r => nIf(Nat.beq fld(e, l, 1) 1, mul r (ys l), r)) m

@[expose] noncomputable def gnK (j : Nat) : Nat := fld(gensLit, Nat.mul 16 j, 65535)

@[expose] noncomputable def rhoK (L i : Nat) : Nat := fld(L, Nat.mul 16 (Nat.shiftLeft 1 i), 65535)

@[expose] noncomputable def linP (L a : Nat) : Bool :=
  Nat.beq fld(L, Nat.mul 16 a, 65535) (wpK mulK 9 (rhoK L) a)

@[expose] noncomputable def comP (L r j : Nat) : Bool :=
  strictB (rhoK L j) fun s => Nat.beq (mulK r s) (mulK s r)

@[expose] noncomputable def invP (L i : Nat) : Bool :=
  strictB (rhoK L i) fun r => bAnd(Nat.beq (mulK r r) 0,
    Nat.rec (motive := fun _ => Bool) true (fun j ih => bAnd(comP L r j, ih)) 9)

@[expose] noncomputable def linB (L : Nat) : Bool :=
  bAnd(Nat.rec (motive := fun _ => Bool) true (fun a ih => bAnd(linP L a, ih)) 512,
    Nat.rec (motive := fun _ => Bool) true (fun i ih => bAnd(invP L i, ih)) 9)

@[expose] noncomputable def cbK (l i : Nat) : Nat :=
  coK (cconj mulK invK (gnK l) (linK (Nat.shiftLeft 1 i)))

@[expose] noncomputable def cbQ (L A l i : Nat) : Bool :=
  Nat.beq (mulK A (rhoK L i)) (mulK (wpK mulK 9 (rhoK L) (cbK l i)) A)

@[expose] noncomputable def cbP (F : Nat → Nat) (L l : Nat) : Bool :=
  strictB (F (gnK l)) fun A =>
    Nat.rec (motive := fun _ => Bool) true (fun i ih => bAnd(cbQ L A l i, ih)) 9

@[expose] noncomputable def stQ (F : Nat → Nat) (P w l : Nat) : Bool :=
  strictB (gnK l) fun g => Nat.beq (F (mulK P g)) (mulK w (F g))

@[expose] noncomputable def stP (F : Nat → Nat) (W e : Nat) : Bool :=
  strictB (wpK mulK 7 gnK e) fun P => strictB fld(W, Nat.mul 16 e, 65535) fun w =>
    Nat.rec (motive := fun _ => Bool) true (fun l ih => bAnd(stQ F P w l, ih)) 7

@[expose] noncomputable def genP (F : Nat → Nat) (z j : Nat) : Bool :=
  strictB (gnK j) fun g => Nat.beq (mulK z g) (mulK (F (F g)) z)

@[expose] noncomputable def homK (k m z : Nat) : Bool :=
  strictB (wLit.getD (16 * k + m - 16) 0) fun W => strictB (lLit.getD k 0) fun L =>
    bAnd(Nat.beq fld(W, 0, 65535) 0, bAnd(Nat.beq (rowFN mulK sNfRow W L 0) 0, bAnd(linB L,
      bAnd(Nat.rec (motive := fun _ => Bool) true
        (fun l ih => bAnd(cbP (rowFN mulK sNfRow W L) L l, ih)) 7,
      bAnd(Nat.rec (motive := fun _ => Bool) true
        (fun e ih => bAnd(stP (rowFN mulK sNfRow W L) W e, ih)) 128,
      Nat.rec (motive := fun _ => Bool) true
        (fun j ih => bAnd(genP (rowFN mulK sNfRow W L) z j, ih)) 9)))))

theorem band_parts {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a
  · exact absurd h Bool.false_ne_true
  · exact ⟨rfl, h⟩

theorem recAll {P : ℕ → Bool} : ∀ {n : ℕ},
    Nat.rec (motive := fun _ => Bool) true (fun e ih => Bool.rec (motive := fun _ => Bool) false ih (P e)) n =
      true → ∀ e < n, P e = true
  | 0, _, e, he => absurd he (Nat.not_lt_zero _)
  | n + 1, h, e, he => by
    obtain ⟨h1, h2⟩ := band_parts h
    rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
    · exact recAll h2 e he
    · exact h1

theorem beq_fld_one (e l : ℕ) : Nat.beq fld(e, l, 1) 1 = e.testBit l := by
  have h : Nat.land (Nat.shiftRight e l) 1 = e / 2 ^ l % 2 := by
    rw [shr_eq]
    exact Nat.and_one_is_mod _
  rw [h, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (e / 2 ^ l) with h2 | h2 <;> rw [h2] <;> rfl

theorem wpK_eq (mul : ℕ → ℕ → ℕ) (ys : ℕ → ℕ) (e : ℕ) : ∀ m, wpK mul m ys e = wprodN mul m ys e
  | 0 => by simp [wpK, wprodN]
  | m + 1 => by
    rw [wprodN_succ, ← wpK_eq mul ys e m]
    change Bool.rec (motive := fun _ => Nat) (wpK mul m ys e) (mul (wpK mul m ys e) (ys m))
      (Nat.beq fld(e, m, 1) 1) = _
    rw [cen_nIf, beq_fld_one]

theorem fld_W (k m e : ℕ) : fld(wLit.getD (16 * k + m - 16) 0, Nat.mul 16 e, 65535) = WK k m e := by
  unfold WK
  rw [show (65535 : ℕ) = 2 ^ 16 - 1 from rfl, fld_eq]
  rfl

theorem fld_L (k a : ℕ) : fld(lLit.getD k 0, Nat.mul 16 a, 65535) = LK k a := by
  unfold LK
  rw [show (65535 : ℕ) = 2 ^ 16 - 1 from rfl, fld_eq]
  rfl

theorem rhoK_eq (k i : ℕ) : rhoK (lLit.getD k 0) i = LK k (2 ^ i) := by
  unfold rhoK
  rw [fld_L, cen_shl, Nat.one_mul]

theorem gnK_eq : ∀ j < 9, gnK j = sGens.getD j 0 := by decide +kernel

theorem gnK_pc {l : ℕ} (hl : l < 7) : gnK l = sPc.getD l 0 := by
  rw [gnK_eq l (by omega)]
  simp only [sGens, List.getD_eq_getElem?_getD, List.getElem?_append_left
    (by simpa [sPc] using hl : l < sPc.length)]

theorem cbK_eq {l : ℕ} (hl : l < 7) (i : ℕ) : cbK l i = sAutData.cb l i := by
  change _ = a9CoTab[sConj (sPc.getD l 0) (a9LinTab[2 ^ i]!)]!
  rw [a9CoTab_get, a9LinTab_get, sConj, sMul_eqK, sInv_eqK, cbK, gnK_pc hl, cen_shl,
    Nat.one_mul]

theorem nfE_eq (x : ℕ) : sAutData.nfE x = nfEK x := by
  simp only [sAutData, sNfTab_get]

theorem nfA_eq (x : ℕ) : sAutData.nfA x = nfAK x := by
  simp only [sAutData, sNfTab_get]

theorem a9K_gens : ∀ g ∈ [128, 34816], a9K.co g < 512 ∧ a9K.lin (a9K.co g) = g := by
  intro g hg
  change a9CoTab[g]! < 512 ∧ a9LinTab[a9CoTab[g]!]! = g
  rw [a9CoTab_get, a9LinTab_get]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl <;> exact ⟨by decide +kernel, by decide +kernel⟩

theorem WK_lt (k m e : ℕ) : WK k m e < 65536 := Nat.mod_lt _ (by norm_num)

theorem LK_lt (k a : ℕ) : LK k a < 65536 := Nat.mod_lt _ (by norm_num)

theorem gK_mul {a b : ℕ} (ha : a < 65536) (hb : b < 65536) :
    SModel.codeIso.g (mulK a b) = SModel.codeIso.g a * SModel.codeIso.g b := by
  apply SModel.codeIso.inj
  rw [SModel.codeIso.map_mul, SModel.codeIso.f_g ha, SModel.codeIso.f_g hb, ← sMul_eqK,
    SModel.codeIso.f_g (sMul_lt a b)]

theorem gK_inj {a b : ℕ} (ha : a < 65536) (hb : b < 65536)
    (h : SModel.codeIso.g a = SModel.codeIso.g b) : a = b := by
  rw [← SModel.codeIso.f_g ha, ← SModel.codeIso.f_g hb, h]

theorem gK_wprodN (ys : ℕ → ℕ) (hys : ∀ l, l < 9 → ys l < 65536) (a : ℕ) :
    wprodN mulK 9 ys a < 65536 ∧
      SModel.codeIso.g (wprodN mulK 9 ys a) = bitProd 9 (fun i => SModel.codeIso.g (ys i)) a := by
  rw [← sMul_eqK]
  exact SModel.codeIso.g_wprodN sMul_zero_zero hys a

theorem sMap_mulS {W ρ φ : ℕ → SModel}
    (hφ : ∀ x, x < 65536 → φ x = W (sAutData.nfE x) * bitProd 9 ρ (sAutData.nfA x))
    (hW0 : W 0 = 1) (h2 : ∀ i, i < 9 → ρ i * ρ i = 1)
    (hc : ∀ i j, i < 9 → j < 9 → ρ i * ρ j = ρ j * ρ i)
    (hcb : ∀ l, l < 7 → ∀ i, i < 9 →
      φ (sPc.getD l 0) * ρ i * (φ (sPc.getD l 0))⁻¹ = bitProd 9 ρ (sAutData.cb l i))
    (hstep : ∀ e, e < 2 ^ 7 → ∀ l, l < 7 →
      φ (sMul (wprodN sMul 7 (fun l' => sPc.getD l' 0) e) (sPc.getD l 0)) = W e * φ (sPc.getD l 0))
    {x : ℕ} (hx : x < 65536) {g : ℕ} (hg : g ∈ sGens) : φ (sMul x g) = φ x * φ g := by
  have hnorm : ∀ x : SModel, KFacts.Mem SModel.codeIso sAutData.K x → ∀ y : SModel,
      KFacts.Mem SModel.codeIso sAutData.K (y * x * y⁻¹) := by
    intro x hx y
    have := sChar SModel.codeIso (MulAut.conj y) x hx
    rw [MulAut.conj_apply] at this
    exact this
  have hgen : (∃ l, l < sAutData.q ∧ g = sAutData.g l) ∨ sAutData.K.In g := by
    rcases List.mem_append.1 hg with hg | hg
    · left
      obtain ⟨l, hl, rfl⟩ := List.mem_iff_getElem.1 hg
      exact ⟨l, hl, (List.getD_eq_getElem _ _ hl).symm⟩
    · right
      exact ⟨(a9K_gens g hg).1, (a9K_gens g hg).2⟩
  exact (sAutFacts sMul_zero_zero).map_mul_gen SModel.codeIso rfl hnorm hφ hW0 h2 hc hcb hstep hx
    hgen

theorem F_mul_gen {F W L : ℕ → ℕ} (hF : ∀ x, F x = mulK (W (nfEK x)) (L (nfAK x)))
    (hWlt : ∀ e, W e < 65536) (hLlt : ∀ a, L a < 65536) (hW0 : W 0 = 0)
    (hlin : ∀ a < 512, L a = wprodN mulK 9 (fun i => L (2 ^ i)) a)
    (hρ2 : ∀ i < 9, mulK (L (2 ^ i)) (L (2 ^ i)) = 0)
    (hρc : ∀ i < 9, ∀ j < 9, mulK (L (2 ^ i)) (L (2 ^ j)) = mulK (L (2 ^ j)) (L (2 ^ i)))
    (hcb : ∀ l < 7, ∀ i < 9, mulK (F (sPc.getD l 0)) (L (2 ^ i)) =
      mulK (wprodN mulK 9 (fun i => L (2 ^ i)) (sAutData.cb l i)) (F (sPc.getD l 0)))
    (hst : ∀ e < 128, ∀ l < 7, F (mulK (wprodN mulK 7 (fun l' => sPc.getD l' 0) e) (sPc.getD l 0)) =
      mulK (W e) (F (sPc.getD l 0)))
    {x : ℕ} (hx : x < 65536) {g : ℕ} (hg : g ∈ sGens) : F (mulK x g) = mulK (F x) (F g) := by
  have hFlt : ∀ x, F x < 65536 := fun x => by rw [hF]; exact mulK_lt _ _
  have hρlt : ∀ l, l < 9 → L (2 ^ l) < 65536 := fun l _ => hLlt _
  have hφ : ∀ x, x < 65536 → SModel.codeIso.g (F x) =
      SModel.codeIso.g (W (sAutData.nfE x)) *
        bitProd 9 (fun i => SModel.codeIso.g (L (2 ^ i))) (sAutData.nfA x) := by
    intro x hx
    rw [nfE_eq, nfA_eq, hF, gK_mul (hWlt _) (hLlt _), hlin _ (nf_lt hx).2,
      (gK_wprodN _ hρlt _).2]
  have hW0' : SModel.codeIso.g (W 0) = 1 := by
    rw [hW0, ← SModel.codeIso.f_one sMul_zero_zero, SModel.codeIso.g_f]
  have h2 : ∀ i, i < 9 → SModel.codeIso.g (L (2 ^ i)) * SModel.codeIso.g (L (2 ^ i)) = 1 := by
    intro i hi
    rw [← gK_mul (hρlt i hi) (hρlt i hi), hρ2 i hi, ← SModel.codeIso.f_one sMul_zero_zero,
      SModel.codeIso.g_f]
  have hc : ∀ i j, i < 9 → j < 9 → SModel.codeIso.g (L (2 ^ i)) * SModel.codeIso.g (L (2 ^ j)) =
      SModel.codeIso.g (L (2 ^ j)) * SModel.codeIso.g (L (2 ^ i)) := by
    intro i j hi hj
    rw [← gK_mul (hρlt i hi) (hρlt j hj), ← gK_mul (hρlt j hj) (hρlt i hi), hρc i hi j hj]
  have hcb' : ∀ l, l < 7 → ∀ i, i < 9 →
      SModel.codeIso.g (F (sPc.getD l 0)) * SModel.codeIso.g (L (2 ^ i)) *
        (SModel.codeIso.g (F (sPc.getD l 0)))⁻¹ =
      bitProd 9 (fun i => SModel.codeIso.g (L (2 ^ i))) (sAutData.cb l i) := by
    intro l hl i hi
    have hB := gK_wprodN _ hρlt (sAutData.cb l i)
    have e := congrArg SModel.codeIso.g (hcb l hl i hi)
    rw [gK_mul (hFlt _) (hρlt i hi), gK_mul hB.1 (hFlt _), hB.2] at e
    rw [e]
    group
  have hstep : ∀ e, e < 2 ^ 7 → ∀ l, l < 7 →
      SModel.codeIso.g (F (sMul (wprodN sMul 7 (fun l' => sPc.getD l' 0) e) (sPc.getD l 0))) =
        SModel.codeIso.g (W e) * SModel.codeIso.g (F (sPc.getD l 0)) := by
    intro e he l hl
    have he' : e < 128 := he
    have h1 := congrArg SModel.codeIso.g (hst e he' l hl)
    rw [gK_mul (hWlt _) (hFlt _)] at h1
    have hs : sMul = mulK := sMul_eqK
    simp only [hs]
    exact h1
  have e := sMap_mulS (W := fun e => SModel.codeIso.g (W e))
    (ρ := fun i => SModel.codeIso.g (L (2 ^ i))) (φ := fun x => SModel.codeIso.g (F x))
    hφ hW0' h2 hc hcb' hstep hx hg
  have hs : sMul = mulK := sMul_eqK
  simp only [hs] at e
  rw [← gK_mul (hFlt _) (hFlt _)] at e
  exact gK_inj (hFlt _) (mulK_lt _ _) e

theorem conj_of_homK {k m z : ℕ} (h : homK k m z = true) (hz : z < 65536) {y : ℕ}
    (hy : y < 65536) : mulK z y = mulK (FK k m (FK k m y)) z := by
  unfold homK at h
  simp only [cen_strictB] at h
  obtain ⟨hW0, h⟩ := band_parts h
  obtain ⟨hF0, h⟩ := band_parts h
  obtain ⟨hlinB, h⟩ := band_parts h
  obtain ⟨hcbB, h⟩ := band_parts h
  obtain ⟨hstB, hgB⟩ := band_parts h
  have hFN : rowFN mulK sNfRow (wLit.getD (16 * k + m - 16) 0) (lLit.getD k 0) = FK k m :=
    funext fun x => FK_eqN k m x
  rw [hFN] at hF0 hcbB hstB hgB
  have hW0' : WK k m 0 = 0 := by
    rw [← fld_W k m 0]
    exact Nat.eq_of_beq_eq_true hW0
  unfold linB at hlinB
  obtain ⟨hlin1, hlin2⟩ := band_parts hlinB
  have hlin : ∀ a < 512, LK k a = wprodN mulK 9 (fun i => LK k (2 ^ i)) a := by
    intro a ha
    have := recAll hlin1 a ha
    unfold linP at this
    have := Nat.eq_of_beq_eq_true this
    rw [fld_L, wpK_eq] at this
    rw [this]
    exact wprodN_congr _ (fun i _ => rhoK_eq k i) a
  have hρ : ∀ i < 9, mulK (LK k (2 ^ i)) (LK k (2 ^ i)) = 0 ∧ ∀ j < 9,
      mulK (LK k (2 ^ i)) (LK k (2 ^ j)) = mulK (LK k (2 ^ j)) (LK k (2 ^ i)) := by
    intro i hi
    have := recAll hlin2 i hi
    unfold invP at this
    simp only [cen_strictB] at this
    obtain ⟨h1, h2⟩ := band_parts this
    rw [rhoK_eq] at h1 h2
    refine ⟨Nat.eq_of_beq_eq_true h1, fun j hj => ?_⟩
    have := recAll h2 j hj
    unfold comP at this
    simp only [cen_strictB] at this
    rw [rhoK_eq] at this
    exact Nat.eq_of_beq_eq_true this
  have hcb : ∀ l < 7, ∀ i < 9, mulK (FK k m (sPc.getD l 0)) (LK k (2 ^ i)) =
      mulK (wprodN mulK 9 (fun i => LK k (2 ^ i)) (sAutData.cb l i)) (FK k m (sPc.getD l 0)) := by
    intro l hl i hi
    have := recAll hcbB l hl
    unfold cbP at this
    simp only [cen_strictB] at this
    have := recAll this i hi
    unfold cbQ at this
    have := Nat.eq_of_beq_eq_true this
    rw [gnK_pc hl, rhoK_eq, wpK_eq, cbK_eq hl] at this
    rw [this]
    congr 1
    exact wprodN_congr _ (fun i _ => rhoK_eq k i) _
  have hst : ∀ e < 128, ∀ l < 7,
      FK k m (mulK (wprodN mulK 7 (fun l' => sPc.getD l' 0) e) (sPc.getD l 0)) =
        mulK (WK k m e) (FK k m (sPc.getD l 0)) := by
    intro e he l hl
    have := recAll hstB e he
    unfold stP at this
    simp only [cen_strictB] at this
    have := recAll this l hl
    unfold stQ at this
    simp only [cen_strictB] at this
    have := Nat.eq_of_beq_eq_true this
    have hg : ∀ l < 7, gnK l = sPc.getD l 0 := fun l hl => gnK_pc hl
    rw [hg l hl, fld_W, wpK_eq, wprodN_congr _ hg] at this
    exact this
  have hmulG : ∀ a < 65536, ∀ g ∈ sGens, FK k m (mulK a g) = mulK (FK k m a) (FK k m g) :=
    fun a ha g hg => F_mul_gen (F := FK k m) (W := WK k m) (L := LK k) (fun _ => rfl) (WK_lt k m)
      (LK_lt k) hW0' hlin (fun i hi => (hρ i hi).1) (fun i hi => (hρ i hi).2) hcb hst ha hg
  have hlt : ∀ a < 65536, FK k m a < 65536 := fun a _ => mulK_lt _ _
  have hF0' : FK k m 0 = 0 := Nat.eq_of_beq_eq_true hF0
  have hFmul : ∀ a < 65536, ∀ c < 65536, FK k m (mulK a c) = mulK (FK k m a) (FK k m c) :=
    fun a ha c hc => mul_of_gens ΦK mulK_zero sGens_lt genK hlt hF0' hmulG ha hc
  have hgen : ∀ g ∈ sGens, mulK z g = mulK (FK k m (FK k m g)) z := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
    have hj9 : j < 9 := hj
    have := recAll hgB j hj9
    unfold genP at this
    simp only [cen_strictB] at this
    have := Nat.eq_of_beq_eq_true this
    rwa [gnK_eq j hj9, List.getD_eq_getElem _ _ hj] at this
  exact conj_of_gens ΦK mulK_zero sGens_lt genK hlt hF0' hFmul hz hgen hy

theorem conjOK_of_hom {k m z : ℕ} (h : homK k m z = true) (hz : z < 65536) :
    ∀ s < 8, conjOK k m z (8192 * s) 8192 = true := by
  intro s hs
  unfold conjOK
  rw [List.all_eq_true]
  intro y hy
  rw [List.mem_range'_1] at hy
  exact beq_iff_eq.2 (conj_of_homK h hz (by omega))

end CertificateChecks.KernelO8.SB3873

end
