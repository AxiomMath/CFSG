module

public import Certificates.Kernel.TwoHSLe4.SO5Eq
public import Certificates.Kernel.TwoHSLe4.CoreA
public import Certificates.Kernel.TwoHSLe4.CoreB
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CertificateChecks.KernelTwoHSLe4.SO5

open CFSG.EvenSporadicStandard.TwoHS

theorem rot_eq (k : ℕ) : pgRotC k = unpk (rotK k) := by
  unfold rotK pgRotC
  rw [sg_eq.2.2.2.2.2.2.1, fmPow_unpk]

theorem refl_eq (k : ℕ) : pgReflC k = unpk (reflK k) := by
  have h : fmPow pgR0C k = unpk (rotK k) := rot_eq k
  unfold reflK pgReflC
  rw [h, sg_eq.2.2.2.2.2.2.2.1, fmMul_unpk]

theorem d0_eq : pgD0Code = D0L.map unpk := by
  simp only [pgD0Code, D0L, List.map_flatMap, List.map_cons, List.map_nil, rot_eq, refl_eq]

theorem c_eq : pgCCode = CL.map unpk := by
  simp only [pgCCode, CL, d0_eq, s0_eq, List.map_flatMap, List.flatMap_map, List.map_map,
    Function.comp_def, fmMul_unpk]

theorem c_cases {a : FM} (ha : a ∈ pgCCode) :
    ∃ d ∈ D0L, ∃ s ∈ S0L, a = unpk (mulK d s) := by
  rw [c_eq] at ha
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  simp only [CL, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨d, hd, s, hs, rfl⟩ := hx
  exact ⟨d, hd, s, hs, rfl⟩

theorem mem_c {x : ℕ} (h : x ∈ CL) : unpk x ∈ pgCCode := by
  rw [c_eq]
  exact List.mem_map_of_mem h

theorem cl_mulK {x : ℕ} (h : x ∈ CL) : ∃ d s, x = mulK d s := by
  simp only [CL, List.mem_flatMap, List.mem_map] at h
  obtain ⟨d, -, s, -, rfl⟩ := h
  exact ⟨d, s, rfl⟩

theorem cl_unpk_inj {x y : ℕ} (hx : x ∈ CL) (hy : y ∈ CL) (h : unpk x = unpk y) : x = y := by
  obtain ⟨d, s, rfl⟩ := cl_mulK hx
  obtain ⟨d', s', rfl⟩ := cl_mulK hy
  exact mulK_inj h

theorem core : PGCoreF := by
  obtain ⟨h1, h2, h3, h4⟩ := c_s0
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ := c_ok
  obtain ⟨so1, so2⟩ := c_so
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14⟩ := c_d0
  have ht : pgTau1C = unpk (SG 0) := sg_eq.1
  have hr : pgR0C = unpk (SG 6) := sg_eq.2.2.2.2.2.2.1
  have hf : pgSf0C = unpk (SG 7) := sg_eq.2.2.2.2.2.2.2.1
  refine ⟨h1, h2, h3, h4, ?_, ?_, o1, o2, o3, o4, o5, o6, ?_, ?_, d1, d2, ?_, ?_, d3, d4, d5,
    d6, d7, d8, d9, d10, d11, d12, d13, d14⟩
  · rw [c_eq, List.length_map]
    decide +kernel
  · rw [c_eq]
    exact List.Nodup.map_on (fun x hx y hy h => cl_unpk_inj hx hy h) k_nodup
  · intro a ha
    obtain ⟨d, hd, s, hs, rfl⟩ := c_cases ha
    have hd' : unpk d ∈ pgD0Code := by rw [d0_eq]; exact List.mem_map_of_mem hd
    have hs' : unpk s ∈ pgS0Code := by rw [s0_eq]; exact List.mem_map_of_mem hs
    rw [← fmMul_unpk]
    refine ⟨fmOk_fmMul (o2 _ hd') (o1 _ hs'), isSO5_fmMul (so2 _ hd') (so1 _ hs'), ?_⟩
    have hc : mulK d s ∈ CL := by
      simp only [CL, List.mem_flatMap, List.mem_map]
      exact ⟨d, hd, s, hs, rfl⟩
    rw [fmMul_unpk, ht, fmMul_unpk, fmMul_unpk,
      beq_iff_eq.1 (List.all_eq_true.1 k_tau _ hc)]
  · intro c hc
    rw [s0_eq] at hc
    obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hc
    have h := List.all_eq_true.1 k_s0 c' hc'
    rw [List.contains_iff_mem] at h
    exact mem_c h
  · intro a ha hcomm
    rw [c_eq] at ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    have h := List.all_eq_true.1 k_cent x hx
    have hpre : (S0L.all fun c => mulK c x == mulK x c ||
        mulK c x == mulK (mulK x (SG 0)) c) = true := by
      rw [List.all_eq_true]
      intro c hc
      have hc' : unpk c ∈ pgS0Code := by rw [s0_eq]; exact List.mem_map_of_mem hc
      rcases hcomm _ hc' with e | e
      · rw [fmMul_unpk, fmMul_unpk] at e
        simp [mulK_inj e]
      · rw [ht, fmMul_unpk, fmMul_unpk, fmMul_unpk] at e
        simp [mulK_inj e]
    rw [hpre] at h
    simp only [Bool.not_true, Bool.false_or, List.contains_iff_mem] at h
    rw [d0_eq]
    exact List.mem_map_of_mem h
  · intro a ha hR hF
    rw [c_eq] at ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    have h := List.all_eq_true.1 k_rs x hx
    rw [hr, fmMul_unpk, fmMul_unpk] at hR
    rw [hf, fmMul_unpk, fmMul_unpk] at hF
    simp only [mulK_inj hR, mulK_inj hF, beq_self_eq_true, Bool.not_true, Bool.false_or,
      Bool.or_eq_true, List.contains_iff_mem] at h
    rw [ht, fmMul_unpk, s0_eq]
    rcases h with h | h
    · exact Or.inl (List.mem_map_of_mem h)
    · exact Or.inr (List.mem_map_of_mem h)

end CertificateChecks.KernelTwoHSLe4.SO5

end
