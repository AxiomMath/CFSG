
module

public import Certificates.Kernel.MonsterB.Ind3034.Checks
public import Certificates.Kernel.MonsterB.IndCandGet

public section

namespace CFSG.KC.Ind3034

open CFSG.Monster.B.Fischer CFSG.KLie.CT CFSG.KC.SortTree CFSG.KC.U6Orb CFSG.KC.Bfs
open CertificateChecks.KernelMonB CertificateChecks.KernelMonB.IndOrbGlue
open CertificateChecks.Batch3031

theorem pts_spec :
    (∀ x, x ∈ dCert.pts ↔ ∃ i < 5760, x = dec (valF 270 (recD i))) ∧
    (∀ x ∈ dCert.pts, dValid x = true) ∧
    (∀ x ∈ dCert.pts, ∀ y ∈ dCert.pts, dKey x = dKey y → x = y) ∧ dCert.pts.size = 5760 := by
  obtain ⟨hrc, hrv⟩ := kRoot
  have hT := kTree
  rw [← hrc] at hT
  obtain ⟨S', hS', hcard, -, -, hmem⟩ := orbit_sound (by norm_num) hT kClose
  have hdec : ∀ a, dValid a = true → dec (code a) = a := fun a ha => dec_code ha
  have hact : ∀ k < 3, ∀ a, dValid a = true → dValid (dAct k a) = true :=
    fun k hk a ha => dAct_valid hk ha
  have hcode : ∀ k < 3, ∀ a, dValid a = true → actC k (code a) = code (dAct k a) :=
    fun k hk a ha => actC_code hk ha
  obtain ⟨hS, hc, hv⟩ := orbit_code (valid := fun a => dValid a = true) hdec hact hcode hrv hS'
  have hrc' := fun c (hc : c ∈ S') => reach_code (valid := fun a => dValid a = true) hdec hact
    hcode hrv ((hS' c).2 hc)
  have hkey : ∀ a ∈ S'.image dec, ∀ b ∈ S'.image dec, dKey a = dKey b → a = b := by
    intro a ha b hb e
    obtain ⟨c1, h1, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨c2, h2, rfl⟩ := Finset.mem_image.1 hb
    have e' := key_inj (hrc' c1 h1).1 (hrc' c2 h2).1 e
    rw [(hrc' c1 h1).2.2, (hrc' c2 h2).2.2] at e'
    obtain ⟨i, hi, rfl⟩ := (hmem c1).1 h1
    obtain ⟨j, hj, rfl⟩ := (hmem c2).1 h2
    rw [hiIncK_sound kKey hi hj e']
  obtain ⟨-, h2, h3, -⟩ := arrBfs_spec (fuel := 6000) (valid := dValid) (S'.image dec) hS hv hkey
    (by rw [hc, hcard]; norm_num)
  have hpts : ∀ x, x ∈ dCert.pts ↔ x ∈ S'.image dec := h2
  have hsize : dCert.pts.size = (S'.image dec).card := h3
  refine ⟨fun x => ?_, fun x hx => hv x ((hpts x).1 hx),
    fun x hx y hy e => hkey x ((hpts x).1 hx) y ((hpts y).1 hy) e, hsize.trans (hc.trans hcard)⟩
  rw [hpts, Finset.mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨i, hi, rfl⟩ := (hmem c).1 hc
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, (hmem _).2 ⟨i, hi, rfl⟩, rfl⟩

theorem dec_get {c t : ℕ} (ht : t < 54) : (dec c)[t]! = fget c (permI t) 5 := by
  rw [getElem!_pos _ t (by simp [dec]; exact ht)]
  simp [dec]

theorem wordL_eq : ∀ w : List ℤ, (wordCat w).toList = wordL w
  | [] => by simp [wordCat, wordL, idArrN]
  | z :: w => by
    have ih := wordL_eq w
    simp only [wordCat, List.foldr_cons] at ih ⊢
    rw [wordL, List.foldr_cons, ← wordL, ← ih, amulN, Array.toList_map]
    refine List.map_congr_left fun x _ => ?_
    rw [← Array.getElem!_toList, List.getElem!_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rfl

theorem zFib_eq {g i : ℕ} (hg : g < 2) (hi : i < 77) : zFib g i = zFibK IG.F g i := by
  rw [zFib, gen_get hg (by omega)]
  rfl

theorem eqPre_sound (c : ℕ) : ∀ (L : List ℕ) (i : ℕ), eqPre c L i = true →
    i + L.length = 22 ∧ ∀ k < L.length, fget c (32 + (i + k)) 5 = L[k]!
  | [], i, h => ⟨by simpa using Nat.eq_of_beq_eq_true h, fun k hk => absurd hk (by simp)⟩
  | a :: L, i, h => by
    have h' : andB (Nat.beq (fget c (Nat.add 32 i) 5) a) (eqPre c L (Nat.succ i)) = true := h
    obtain ⟨h1, h2⟩ := andB_true_iff.1 h'
    obtain ⟨hl, hk⟩ := eqPre_sound c L (i + 1) h2
    refine ⟨by simp only [List.length_cons]; omega, fun k hk' => ?_⟩
    cases k with
    | zero =>
      rw [List.getElem!_cons_zero, Nat.add_zero]
      exact Nat.eq_of_beq_eq_true h1
    | succ k =>
      rw [List.getElem!_cons_succ, ← hk k (by simp only [List.length_cons] at hk'; omega)]
      congr 2
      omega

theorem zFrom_sound (G rec : ℕ → ℕ) : ∀ (L : List ℕ) (n : ℕ), zFrom G rec L n = true →
    n + L.length = 154 ∧ ∀ k < L.length, zOne G rec ((n + k) / 77) ((n + k) % 77) L[k]! = true
  | [], n, h => ⟨by simpa using Nat.eq_of_beq_eq_true h, fun k hk => absurd hk (by simp)⟩
  | r :: L, n, h => by
    have h' : andB (zOne G rec (Nat.div n 77) (Nat.mod n 77) r) (zFrom G rec L (Nat.succ n)) =
      true := h
    obtain ⟨h1, h2⟩ := andB_true_iff.1 h'
    obtain ⟨hl, hk⟩ := zFrom_sound G rec L (n + 1) h2
    refine ⟨by simp only [List.length_cons]; omega, fun k hk' => ?_⟩
    cases k with
    | zero =>
      rw [List.getElem!_cons_zero, Nat.add_zero]
      exact h1
    | succ k =>
      rw [List.getElem!_cons_succ]
      have := hk k (by simp only [List.length_cons] at hk'; omega)
      rwa [Nat.add_assoc, Nat.add_comm 1 k] at this

theorem zOne_get {g i : ℕ} (hg : g < 2) (hi : i < 77) :
    ∃ r < 5760, zFibK IG.F g i < 77 ∧
      (∀ t < 22, fget (valF 270 (recD r)) (32 + t) 5 = (wordL (kappaW (zFibK IG.F g i) g i))[t]!) ∧
      (wordL (kappaW (zFibK IG.F g i) g i)).length = 22 ∧
      ∀ q < 32, fget (IG.F g) (1046 + 32 * i + q) 12 =
        1046 + 32 * zFibK IG.F g i + fget (valF 270 (recD r)) q 5 := by
  obtain ⟨hl, hk⟩ := zFrom_sound _ _ _ 0 kZ
  have hn : 77 * g + i < CFSG.KD.I3034.W.c0.length := by omega
  have h := hk _ hn
  rw [Nat.zero_add, show (77 * g + i) / 77 = g by omega, show (77 * g + i) % 77 = i by omega] at h
  have h' : andB (Nat.blt _ 5760) (andB (Nat.blt (zFibK IG.F g i) 77)
    (andB (eqPre (valF 270 (recD _)) (wordL (kappaW (zFibK IG.F g i) g i)) 0) _)) = true := h
  obtain ⟨h1, h2⟩ := andB_true_iff.1 h'
  obtain ⟨h3, h4⟩ := andB_true_iff.1 h2
  obtain ⟨h5, h6⟩ := andB_true_iff.1 h4
  obtain ⟨hl', hk'⟩ := eqPre_sound _ _ 0 h5
  rw [Nat.zero_add] at hl'
  refine ⟨_, blt_iff.1 h1, blt_iff.1 h3, fun t ht => ?_, hl', fun q hq => ?_⟩
  · rw [← hk' t (by omega), Nat.zero_add]
  · exact Nat.eq_of_beq_eq_true ((SortTree.allN_iff _ _).1 h6 q hq)

theorem dFind_get {κ y : Array ℕ} (hy : y ∈ dCert.pts) (hyκ : y.extract 0 22 = κ) :
    dFind κ < dCert.pts.size ∧ dCert.pts[dFind κ]! = y := by
  obtain ⟨-, -, hkey, -⟩ := pts_spec
  have hex : ∃ x ∈ dCert.pts, (x.extract 0 22 == κ) = true := ⟨y, hy, by simp [hyκ]⟩
  have hp : dFind κ < dCert.pts.size := Array.findIdx_lt_size_of_exists hex
  have hpx : (dCert.pts[dFind κ].extract 0 22 == κ) = true := Array.findIdx_getElem (w := hp)
  refine ⟨hp, ?_⟩
  rw [getElem!_pos dCert.pts _ hp]
  refine hkey _ (Array.getElem_mem hp) y hy ?_
  rw [dKey, dKey, beq_iff_eq.1 hpx, hyκ]

theorem zCheck_of {g i : ℕ} {y : Array ℕ} (hy : y ∈ dCert.pts)
    (hyκ : y.extract 0 22 = wordCat (kappaWord g i)) (hj : zFib g i < 77)
    (hfib : ∀ q < 32, (indM22Gen g)[1046 + 32 * i + q]! = 1046 + 32 * zFib g i + y[22 + q]!) :
    zCheckOne g i = true := by
  obtain ⟨hp, hx⟩ := dFind_get hy hyκ
  unfold zCheckOne
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range]
  rw [hx]
  exact ⟨⟨⟨hp, hyκ⟩, hj⟩, hfib⟩

theorem kappa_toList {g i : ℕ} (hg : g < 2) (hi : i < 77) :
    (wordCat (kappaWord g i)).toList = wordL (kappaW (zFibK IG.F g i) g i) := by
  rw [wordL_eq, kappaWord, zFib_eq hg hi, kappaW]

theorem dec_size (c : ℕ) : (dec c).size = 54 := by simp [dec]

theorem dec_extract {c : ℕ} {κ : Array ℕ} {L : List ℕ} (hκ : κ.toList = L) (hlen : L.length = 22)
    (hpre : ∀ t < 22, fget c (32 + t) 5 = L[t]!) : (dec c).extract 0 22 = κ := by
  apply Array.ext
  · rw [Array.size_extract, dec_size, ← Array.length_toList, hκ, hlen]
    rfl
  · intro t h1 h2
    have ht : t < 22 := by simpa [dec_size] using h1
    rw [Array.getElem_extract]
    simp only [Nat.zero_add]
    rw [← getElem!_pos (dec c) t (by rw [dec_size]; omega), dec_get (by omega)]
    have : permI t = 32 + t := by simp [permI, ht]
    rw [this, hpre t ht, getElem!_pos L t (by rw [hlen]; exact ht)]
    subst hκ
    rfl

theorem zCheck {g i : ℕ} (hg : g < 2) (hi : i < 77) : zCheckOne g i = true := by
  obtain ⟨hmem, -, -, -⟩ := pts_spec
  obtain ⟨r, hr, hj, hpre, hlen, hfib⟩ := zOne_get hg hi
  have hy : dec (valF 270 (recD r)) ∈ dCert.pts := (hmem _).2 ⟨r, hr, rfl⟩
  have hz := zFib_eq hg hi
  refine zCheck_of hy (dec_extract (kappa_toList hg hi) hlen hpre) (hz ▸ hj) fun q hq => ?_
  rw [gen_get hg (by omega), hfib q hq, dec_get (by omega), hz]
  have : permI (22 + q) = q := by simp [permI]
  rw [this]

theorem check_X : ∀ g < 2, ∀ t < 22, (indM22Gen g)[t]! = genAB' g t := by
  intro g hg t ht
  rw [gen_get hg (by omega)]
  exact Nat.eq_of_beq_eq_true ((SortTree.allN_iff _ _).1 ((SortTree.allN_iff _ _).1 kX g hg) t ht)

theorem check_W : ∀ g < 2, ∀ u < 1024, (indM22Gen g)[22 + u]! = 22 + linW g u := by
  intro g hg u hu
  rw [gen_get hg (by omega)]
  exact Nat.eq_of_beq_eq_true ((SortTree.allN_iff _ _).1 ((SortTree.allN_iff _ _).1 kW g hg) u hu)

theorem check_Z : (List.range 2).all (fun g => (List.range 77).all (zCheckOne g)) = true := by
  simp only [List.all_eq_true, List.mem_range]
  exact fun g hg i hi => zCheck hg hi

theorem check_D : ∀ p < 5760, ∀ q < 32, (dCert.pts[p]!)[22 + q]! < 32 := by
  obtain ⟨-, hval, -, hsize⟩ := pts_spec
  intro p hp q hq
  have hm : dCert.pts[p]! ∈ dCert.pts := by
    rw [getElem!_pos _ p (by omega)]
    exact Array.getElem_mem _
  exact (valid_get (hval _ hm)).2.2 (22 + q) (by omega) (by omega)

theorem zShift_eq {t i : ℕ} (ht : t < 10) (hi : i < 77) : zShift t i = zShiftK ITr.F t i := by
  rw [zShift, IndCand.trans_get ht (by omega)]
  rfl

theorem check_T : ∀ t < 10, (∀ n < 22, (indTransGen t)[n]! = n) ∧
    (∀ u < 1024, (indTransGen t)[22 + u]! = 22 + (u ^^^ 2 ^ t)) ∧
    ∀ i < 77, zShift t i < 32 ∧ ∀ q < 32,
      (indTransGen t)[1046 + 32 * i + q]! = 1046 + 32 * i + (q ^^^ zShift t i) := by
  intro t ht
  obtain ⟨h1, h2⟩ := andB_true_iff.1 ((SortTree.allN_iff _ _).1 kT t ht)
  obtain ⟨h2, h3⟩ := andB_true_iff.1 h2
  refine ⟨fun n hn => ?_, fun u hu => ?_, fun i hi => ?_⟩
  · rw [IndCand.trans_get ht (by omega)]
    exact Nat.eq_of_beq_eq_true ((SortTree.allN_iff _ _).1 h1 n hn)
  · rw [IndCand.trans_get ht (by omega)]
    exact Nat.eq_of_beq_eq_true ((SortTree.allN_iff _ _).1 h2 u hu)
  · obtain ⟨h4, h5⟩ := andB_true_iff.1 ((SortTree.allN_iff _ _).1 h3 i hi)
    rw [zShift_eq ht hi]
    refine ⟨blt_iff.1 h4, fun q hq => ?_⟩
    rw [IndCand.trans_get ht (by omega)]
    exact Nat.eq_of_beq_eq_true ((SortTree.allN_iff _ _).1 h5 q hq)

theorem check_S : ∀ t < 10, ∀ i < 77,
    red 17 pivQ rowQ (wordMask (invWord (blockWord i)) (spreadW (2 ^ t)) ^^^
      spreadQ (zShift t i)) = 0 := by
  intro t ht i hi
  rw [zShift_eq ht hi]
  exact Nat.eq_of_beq_eq_true ((SortTree.allN_iff _ _).1 ((SortTree.allN_iff _ _).1 kS t ht) i hi)

theorem check_size : ∀ g < 2, (indM22Gen g).size = 3510 := by
  intro g _
  simp only [indM22Gen, hexTable3, Array.size_ofFn]

end CFSG.KC.Ind3034

end
