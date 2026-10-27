module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundLetters
public import Certificates.Kernel.G24Cls.Chk27209
public import Certificates.Kernel.G24Cls.C26992
public import Certificates.Kernel.Co1B.C27207

public section

set_option maxRecDepth 400000
set_option linter.unusedSectionVars false

namespace CertificateChecks.KernelG24.Norm27209

open CFSG.KC.Enum CFSG.KC.G24Key CFSG.KC.G24Word CertificateChecks.KernelG24.Tri27206
  CertificateChecks.KernelG24.Cls27203 CertificateChecks.KernelG24.Dih26992
  CFSG.EvenSporadicStandard.G24Aut CFSG.EvenSporadicStandard.Co1Cent CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier.Native

theorem wordM_eq_prod {M : Type*} [Group M] (gs : List M) (w : List ℤ) :
    wordM gs w = (w.map (letterM gs)).prod := by
  unfold wordM
  suffices ∀ x : M, w.foldl (fun x j => x * letterM gs j) x = x * (w.map (letterM gs)).prod by
    simpa using this 1
  induction w with
  | nil => intro x; simp
  | cons j w ih =>
    intro x
    rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, mul_assoc]

theorem letterM_decLetter {M : Type*} [Group M] (a b : M) {c : ℕ} (h2 : 2 ≤ c) (h5 : c ≤ 5) :
    letterM [a, b] (decLetter c) =
      if c = 2 then a else if c = 3 then a⁻¹ else if c = 4 then b else b⁻¹ := by
  interval_cases c <;> simp [letterM, decLetter]


theorem wordM_eq_wordL {w : List ℕ} (hw : ∀ c ∈ w, 2 ≤ c ∧ c ≤ 5) :
    wordM [xBar, yBar] (w.map decLetter) = wordL xBar yBar w := by
  rw [wordM_eq_prod, wordL, List.map_map]
  congr 1
  refine List.map_congr_left fun c hc => ?_
  rw [Function.comp_apply, letterM_decLetter _ _ (hw c hc).1 (hw c hc).2]
  rfl

theorem sWords_getD (j : ℕ) :
    sWords.getD j [] = (KernelCo1B.Cent27207.K.SW.getD j []).map decLetter := by
  rw [KernelCo1B.Cent27207.sWords_eq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_map]
  cases KernelCo1B.Cent27207.K.SW[j]? <;> rfl

theorem norm_facts : ∀ j < 6, ∀ i < 8,
    wordM [xBar, yBar] (sWords.getD j []) * gR i * (wordM [xBar, yBar] (sWords.getD j []))⁻¹ ∈
      Subgroup.closure (gR '' Set.Iio 8) := by
  classical
  have kCan' := Cls27203.kCan
  have kSift' := Cls27203.kSift
  simp only [Bool.and_eq_true] at kCan' kSift'
  have hγD : ∀ i < 8, gR i ∈ twoBD := fun i hi =>
    mem_of_sift (rep_of_invEqK (CFSG.KC.Pack.allN_spec Cls27203.kInv i hi)).1
      (CFSG.KC.Pack.allN_spec kCan'.1 i hi) (CFSG.KC.Pack.allN_spec kSift'.1.1 i hi)
  set T := Subgroup.closure (gR '' Set.Iio 8) with hTdef
  have hTD : T ≤ twoBD := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact hγD j hj
  have hgRl : ∀ l, gRl l ∈ T := fun l => Subgroup.subset_closure ⟨_, land7_lt l, rfl⟩
  have hkey : ∀ k < 4096, keyT k = keyE (treeE gRl TP TG 8 k) := treeK_spec ptT kTree
  intro j hj i hi
  obtain ⟨hw, hn⟩ := normJ_spec ptL ptLI (fun i hi => ptRG hi) (CFSG.KC.Pack.allN_spec kNorm j hj)
  obtain ⟨hk, he⟩ := hn i hi
  set w := KernelCo1B.Cent27207.K.SW.getD j []
  have hπ : wordM [xBar, yBar] (sWords.getD j []) = (w.map (letE xBar yBar)).prod := by
    rw [sWords_getD, wordM_eq_wordL hw]
    rfl
  rw [hπ]
  have hπD : (w.map (letE xBar yBar)).prod ∈ twoBD := wordL_mem hxD hyD w
  have heq := twoBD_eq_of_keyE (mul_mem (mul_mem hπD (hγD i hi)) (inv_mem hπD))
    (hTD (treeE_mem hgRl TP TG 8 _)) (he.symm.trans (hkey _ hk))
  rw [heq]
  exact treeE_mem hgRl TP TG 8 _

theorem norm_ok : ∀ j < 6, ∀ i < 8,
    wordM [permOfArr 1365 xa, permOfArr 1365 ya] (sWords.getD j []) * permOfArr 1365 rdGens[i]! *
        (wordM [permOfArr 1365 xa, permOfArr 1365 ya] (sWords.getD j []))⁻¹ ∈
      Subgroup.closure ((fun j => permOfArr 1365 rdGens[j]!) '' {j | j < 8}) := by
  have hX : permOfArr 1365 xa = xBar := strong0_eq
  have hY : permOfArr 1365 ya = yBar := strong1_eq
  have hset : (fun j => permOfArr 1365 rdGens[j]!) '' {j | j < 8} = gR '' Set.Iio 8 :=
    Set.image_congr fun j hj => perm_rdGens hj
  rw [hX, hY, hset]
  intro j hj i hi
  rw [perm_rdGens hi]
  exact norm_facts j hj i hi

end CertificateChecks.KernelG24.Norm27209

end
