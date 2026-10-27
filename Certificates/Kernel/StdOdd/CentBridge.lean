module

public import Certificates.Kernel.StdOdd.RootOrbitBridge
public import CFSG.Certificates.Kernel.StdOdd.ChainSound
public import CFSG.Monster.Existence.StdOdd.Cert.CentFacts

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain CFSG.KS.StdOdd.Orbit CFSG.KS.StdOdd.Chain
  CFSG.KD.StdOdd.Orbit CFSG.KC.Misc.E6Std CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.Existence.StdOdd.Cert Matrix

@[expose] def vecK (v : ℕ) : Fin 78 → K := fun k => ofBits (v.testBit (2 * k)) (v.testBit (2 * k + 1))

theorem flat_vecK (v : ℕ) : flat (vecK v) = vecB v := by
  ext j
  obtain ⟨⟨k, a⟩, rfl⟩ := eqv.surjective j
  rw [flat_eqv]
  simp only [vecK, vecB, bz, blkF_ofBits, eqv_val]
  rcases a with ⟨_ | _ | a, ha⟩
  · simp [bb, toZ_eq_ite]
  · have e : 1 + 2 * (k : ℕ) = 2 * k + 1 := Nat.add_comm _ _
    simp [bb, toZ_eq_ite, e]
  · omega

theorem ptK_eq_vecK {U : List ℕ} {i v : ℕ} (h : ptB U i = vecB v) : ptK U i = vecK v :=
  flat_inj (by rw [flat_ptK, flat_vecK, h])

theorem ptK_inj {U V : List ℕ} {i j : ℕ} (h : ptK U i = ptK V j) : ptB U i = ptB V j := by
  rw [← flat_ptK, ← flat_ptK, h]

theorem ptB_inj {U V : List ℕ} {i j : ℕ} (h : ptB U i = ptB V j) : ptK U i = ptK V j :=
  flat_inj (by rw [flat_ptK, flat_ptK, h])

theorem ptK_mapRows {U : List ℕ} (hl : lenN U = 156) {N : ℕ} {M : Matrix (Fin 78) (Fin 78) K}
    (hN : Rep N M) (i : ℕ) : ptK (mapRows N U) i = M *ᵥ ptK U i := by
  apply flat_inj
  rw [flat_ptK, planeApply_sound hl, matB_eq_decB, hN.2, flat_mulVec, flat_ptK]

theorem walk_lift {Ms : List ℕ} {Ks : List (Matrix (Fin 78) (Fin 78) K)} (hlen : lenN Ms = Ks.length)
    (hrep : ∀ l < lenN Ms, Rep (nthN Ms l) (Ks.getD l 0)) :
    ∀ (S : List (List ℕ)) (i : ℕ), ∃ g ∈ monL Ks, blowM g = walkElt Ms S i := by
  have hsel : ∀ (Ns : List ℕ) (Ls : List (Matrix (Fin 78) (Fin 78) K)) (ms : List ℕ) (i : ℕ),
      lenN Ns = Ls.length → (∀ l < lenN Ns, Rep (nthN Ns l) (Ls.getD l 0)) →
      (∀ M ∈ Ls, M ∈ monL Ks) → ∃ g ∈ monL Ks, blowM g = selM Ns ms i := by
    intro Ns
    induction Ns with
    | nil => intro Ls ms i _ _ _; exact ⟨1, Submonoid.one_mem _, by rw [blowM_one]; rfl⟩
    | cons N Ns ih =>
      intro Ls ms i hl hr hm
      cases Ls with
      | nil => simp [lenN] at hl
      | cons L Ls =>
        cases ms with
        | nil => exact ⟨1, Submonoid.one_mem _, by rw [blowM_one]; rfl⟩
        | cons m ms =>
          rw [selM]
          split_ifs
          · refine ⟨L, hm L List.mem_cons_self, ?_⟩
            have := hr 0 (by rw [lenN_cons]; omega)
            rw [nthN_cons_zero, List.getD_cons_zero] at this
            rw [matB_eq_decB, this.2]
          · refine ih Ls ms i (by rw [lenN_cons] at hl; simpa using hl) (fun l hl' => ?_)
              (fun M hM => hm M (List.mem_cons_of_mem _ hM))
            have := hr (l + 1) (by rw [lenN_cons]; omega)
            rwa [nthN_cons_succ, List.getD_cons_succ] at this
  intro S i
  induction S with
  | nil => exact ⟨1, Submonoid.one_mem _, by rw [blowM_one]; rfl⟩
  | cons ms S ih =>
    obtain ⟨g, hg, hge⟩ := ih
    obtain ⟨h, hh, hhe⟩ := hsel Ms Ks ms i hlen hrep (fun M hM => Submonoid.subset_closure hM)
    exact ⟨g * h, Submonoid.mul_mem _ hg hh, by rw [blowM_mul, hge, hhe, walkElt]⟩

theorem ptK_walk {U V : List ℕ} {Ms : List ℕ} {S : List (List ℕ)} {g : Matrix (Fin 78) (Fin 78) K}
    {i : ℕ} (hV : ptB V i = walkElt Ms S i *ᵥ ptB U i) (hg : blowM g = walkElt Ms S i) :
    ptK V i = g *ᵥ ptK U i := by
  apply flat_inj
  rw [flat_ptK, hV, flat_mulVec, hg, flat_ptK]

theorem ptK_repl (v w i : ℕ) (hi : i < w) : ptK (repl v w) i = vecK v :=
  ptK_eq_vecK (repl_sound v w i hi)

theorem ptK_of_neqV {U : List ℕ} (hl : lenN U = 156) {v w : ℕ} (h : Nat.beq (neqV U v w) 0 = true)
    {i : ℕ} (hi : i < w) : ptK U i = vecK v := by
  apply ptK_eq_vecK
  by_contra hne
  have := (neqV_sound hl v w i).2 ⟨hi, hne⟩
  rw [Nat.eq_of_beq_eq_true h, Nat.zero_testBit] at this
  cases this

end CFSG.KD.StdOdd.Cent

end
