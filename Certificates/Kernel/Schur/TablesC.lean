module

public import Certificates.Kernel.Schur.Tables
public import CFSG.Certificates.Kernel.Schur.Words
public import CFSG.Certificates.Kernel.CosetBounds

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelSchur

open CFSG.Certificates CFSG.Certificates.KB CFSG.KC.SchurC

@[expose] def oddWords : List (List (ℕ × Bool)) :=
  CFSG.KC.Schur.Words.odds.map fun w => (List.replicate 4 w).flatten

abbrev TabBound {E : Type*} [Group E] (gen : ℕ → E) : Prop :=
  wordSub gen oddWords ≤ Subgroup.closure (gen '' {g | g < 3}) ∧
    (wordSub gen oddWords).relIndex (Subgroup.closure (gen '' {g | g < 3})) ≠ 0 ∧
    (wordSub gen oddWords).relIndex (Subgroup.closure (gen '' {g | g < 3})) ≤ 24

theorem table_bound {E : Type*} [Group E] (gen : ℕ → E) {rels : List (List (ℕ × Bool))}
    {inv L eps nLab nT N RW RM nR nS nW nF : ℕ} {F D Wd Wd2 R S : ℕ → ℕ} {amap : ℕ}
    {words : List (List (ℕ × Bool))} {walk cov : List ℕ}
    (h1 : tableOk inv L eps nLab nT N RW RM nR nS nW nF F D Wd Wd2 R S amap rels words walk cov =
      true) (hN : N ≤ 24) (hw : words = oddWords) (htop : topOk amap 3 = true)
    (h : ∀ r ∈ rels, sword gen r = 1) : TabBound gen := by
  have b := tableOk_sound gen h h1
  have hs : {g | inAlpha amap g} = {g | g < 3} :=
    Set.ext fun g => topOk_sound (n := 3) (by norm_num) htop g
  rw [alphaSub, hs, hw] at b
  exact ⟨b.1, b.2.1, b.2.2.trans hN⟩

theorem tc01 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels true false false false false, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC01.t1
  unfold CFSG.KBRoute.SchurC01.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC01.top h

theorem tc02 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels false true false false false, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC02.t1
  unfold CFSG.KBRoute.SchurC02.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC02.top h

theorem tc03 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels true true false false false, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC03.t1
  unfold CFSG.KBRoute.SchurC03.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC03.top h

theorem tc04 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels false false true false false, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC04.t1
  unfold CFSG.KBRoute.SchurC04.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC04.top h

theorem tc05 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels true false true false false, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC05.t1
  unfold CFSG.KBRoute.SchurC05.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC05.top h

theorem tc06 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels false true true false false, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC06.t1
  unfold CFSG.KBRoute.SchurC06.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC06.top h

theorem tc07 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels true true true false false, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC07.t1
  unfold CFSG.KBRoute.SchurC07.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC07.top h

theorem tc08 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels false false false true false, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC08.t1
  unfold CFSG.KBRoute.SchurC08.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC08.top h

theorem tc09 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels true false false true false, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC09.t1
  unfold CFSG.KBRoute.SchurC09.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC09.top h

theorem tc10 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels false true false true false, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC10.t1
  unfold CFSG.KBRoute.SchurC10.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC10.top h

theorem tc11 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels true true false true false, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC11.t1
  unfold CFSG.KBRoute.SchurC11.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC11.top h

theorem tc12 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels false false true true false, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC12.t1
  unfold CFSG.KBRoute.SchurC12.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC12.top h

theorem tc13 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels true false true true false, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC13.t1
  unfold CFSG.KBRoute.SchurC13.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC13.top h

theorem tc14 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels false true true true false, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC14.t1
  unfold CFSG.KBRoute.SchurC14.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC14.top h

theorem tc15 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels true true true true false, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC15.t1
  unfold CFSG.KBRoute.SchurC15.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC15.top h

theorem tc16 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels false false false false true, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC16.t1
  unfold CFSG.KBRoute.SchurC16.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC16.top h

theorem tc17 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels true false false false true, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC17.t1
  unfold CFSG.KBRoute.SchurC17.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC17.top h

theorem tc18 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels false true false false true, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC18.t1
  unfold CFSG.KBRoute.SchurC18.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC18.top h

theorem tc19 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels true true false false true, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC19.t1
  unfold CFSG.KBRoute.SchurC19.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC19.top h

theorem tc20 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels false false true false true, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC20.t1
  unfold CFSG.KBRoute.SchurC20.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC20.top h

theorem tc21 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels true false true false true, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC21.t1
  unfold CFSG.KBRoute.SchurC21.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC21.top h

theorem tc22 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels false true true false true, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC22.t1
  unfold CFSG.KBRoute.SchurC22.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC22.top h

theorem tc23 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels true true true false true, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC23.t1
  unfold CFSG.KBRoute.SchurC23.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC23.top h

theorem tc24 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels false false false true true, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC24.t1
  unfold CFSG.KBRoute.SchurC24.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC24.top h

theorem tc25 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels true false false true true, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC25.t1
  unfold CFSG.KBRoute.SchurC25.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC25.top h

theorem tc26 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels false true false true true, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC26.t1
  unfold CFSG.KBRoute.SchurC26.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC26.top h

theorem tc27 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels true true false true true, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC27.t1
  unfold CFSG.KBRoute.SchurC27.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC27.top h

theorem tc28 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels false false true true true, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC28.t1
  unfold CFSG.KBRoute.SchurC28.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC28.top h

theorem tc29 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels true false true true true, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC29.t1
  unfold CFSG.KBRoute.SchurC29.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC29.top h

theorem tc30 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels false true true true true, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC30.t1
  unfold CFSG.KBRoute.SchurC30.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC30.top h

theorem tc31 {E : Type*} [Group E] (gen : ℕ → E)
    (h : ∀ r ∈ crels true true true true true, sword gen r = 1) : TabBound gen := by
  have h1 := SchurC31.t1
  unfold CFSG.KBRoute.SchurC31.T1.ok at h1
  exact table_bound gen h1 (by decide) (by decide +kernel) CFSG.KBRoute.SchurC31.top h

theorem bound_c {E : Type*} [Group E] (gen : ℕ → E) (c0 c1 c2 c3 c4 : Bool)
    (hne : c0 = true ∨ c1 = true ∨ c2 = true ∨ c3 = true ∨ c4 = true)
    (h : ∀ r ∈ crels c0 c1 c2 c3 c4, sword gen r = 1) : TabBound gen := by
  cases c0 <;> cases c1 <;> cases c2 <;> cases c3 <;> cases c4
  · simp at hne
  · exact tc16 gen h
  · exact tc08 gen h
  · exact tc24 gen h
  · exact tc04 gen h
  · exact tc20 gen h
  · exact tc12 gen h
  · exact tc28 gen h
  · exact tc02 gen h
  · exact tc18 gen h
  · exact tc10 gen h
  · exact tc26 gen h
  · exact tc06 gen h
  · exact tc22 gen h
  · exact tc14 gen h
  · exact tc30 gen h
  · exact tc01 gen h
  · exact tc17 gen h
  · exact tc09 gen h
  · exact tc25 gen h
  · exact tc05 gen h
  · exact tc21 gen h
  · exact tc13 gen h
  · exact tc29 gen h
  · exact tc03 gen h
  · exact tc19 gen h
  · exact tc11 gen h
  · exact tc27 gen h
  · exact tc07 gen h
  · exact tc23 gen h
  · exact tc15 gen h
  · exact tc31 gen h

end CertificateChecks.KernelSchur

end
