
module

public import Certificates.Kernel.MonsterB.IndOrbChecks
public import CFSG.Certificates.Kernel.MonsterB.IndOrbSound
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CertificateChecks.KernelMonB.IndOrbGlue

open CFSG.KC.IndOrb CFSG.KC.U6Orb CFSG.KLie.CT CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA.Census
open CertificateChecks.KernelMonB CertificateChecks.KernelMonB.IndOrbChecks

theorem pg_eq (w X t : ℕ) : CFSG.KC.Enum.pg w (CFSG.KS.mask w) X t = fget X t w := by
  change (X >>> (w * t)) &&& CFSG.KS.mask w = (X >>> (t * w)) &&& maskN w
  rw [Nat.mul_comm]
  rfl

theorem gen_get {g y : ℕ} (hg : g < 2) (hy : y < 3510) : (indM22Gen g)[y]! = fget (IG.F g) y 12 := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound IG.all g hg
  rw [← IG.eq] at h
  change (hexTable3 3510 (3510 * g) indM22GenHex)[y]! = _
  rw [h, CFSG.KS.Raw.Orb.unpack_get hy, pg_eq]

theorem gen2_get {g y : ℕ} (hg : g < 2) (hy : y < 3510) :
    (indM22Gen g)[y]! = fget (gen2 (IG.F 0) (IG.F 1) g) y 12 := by
  rw [gen_get hg hy]
  rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl
  · rfl
  · rw [gen2_ne one_ne_zero]

theorem indAB_eq' {g : ℕ} (hg : g < 2) : indAB g = indM22Gen g := by
  rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl
  · simp only [indAB, ↓reduceIte, indA]
  · simp only [indAB, one_ne_zero, ↓reduceIte, indB]

theorem indAB_get {g n : ℕ} (hg : g < 2) (hn : n < 2464) :
    (indAB g)[1046 + n]! = fget (gen2 (IG.F 0) (IG.F 1) g) (1046 + n) 12 := by
  rw [indAB_eq' hg]
  exact gen2_get hg (by omega)

theorem zAct_eq {g n : ℕ} (hg : g < 2) (hn : n < 2464) :
    zActK (IG.F 0) (IG.F 1) 1046 g n = zAct g n := by
  unfold zAct
  rw [indAB_get hg hn]
  unfold zActK
  simp only [Nat.add_eq, Nat.sub_eq]

theorem range_gen {g : ℕ} (hg : g < 2) :
    (∀ i < 3510, fget (IG.F g) i 12 < 3510) ∧ ∀ i < 2464, 1046 ≤ fget (IG.F g) (1046 + i) 12 := by
  rcases (by omega : g = 0 ∨ g = 1) with rfl | rfl
  · exact rangeOK_sound kRange0
  · exact rangeOK_sound kRange1

theorem zAct_range' : ∀ g < 2, ∀ n < 2464,
    1046 ≤ (indAB g)[1046 + n]! ∧ (indAB g)[1046 + n]! < 3510 := by
  intro g hg n hn
  rw [indAB_eq' hg, gen_get hg (by omega)]
  exact ⟨(range_gen hg).2 n hn, (range_gen hg).1 _ (by omega)⟩

noncomputable abbrev wL (o n : ℕ) : List ℕ := orbL (IW 0) 12 o n

noncomputable abbrev zL (o n : ℕ) : List ℕ := orbL (IZ 0) 12 o n

theorem wBfs {s o n D : ℕ} (h : orbOK linW 2 (IW 0) 12 o n D 12 s = true) (hn : 0 < n)
    (hon : o + n ≤ 1024) (hf : n ≤ 1100) :
    (wCert s).pts = (wL o n).toArray ∧
      natCertOK linW 2 (fun u => decide (u < 1024)) s (wCert s) = true :=
  orbOK_natBfs (fun _ _ _ _ => rfl) kWInv h hn hon hf

theorem zBfs {s o n D : ℕ} (h : orbOK zA 2 (IZ 0) 12 o n D 12 s = true) (hn : 0 < n)
    (hon : o + n ≤ 2464) (hf : n ≤ 2500) :
    (zCert s).pts = (zL o n).toArray ∧
      natCertOK zAct 2 (fun n => decide (n < 2464)) s (zCert s) = true :=
  orbOK_natBfs (fun _ hk _ hx => zAct_eq hk hx) kZInv h hn hon hf

theorem w0 : (wCert 0).pts.toList = wL 0 1 := by
  rw [(wBfs kW0 (by norm_num) (by norm_num) (by norm_num)).1]

theorem w1 : (wCert 1).pts.toList = wL 1 22 := by
  rw [(wBfs kW1 (by norm_num) (by norm_num) (by norm_num)).1]

theorem w3 : (wCert 3).pts.toList = wL 23 231 := by
  rw [(wBfs kW3 (by norm_num) (by norm_num) (by norm_num)).1]

theorem w7 : (wCert 7).pts.toList = wL 254 770 := by
  rw [(wBfs kW7 (by norm_num) (by norm_num) (by norm_num)).1]

theorem z0 : (zCert 0).pts.toList = zL 0 462 := by
  rw [(zBfs kZ0 (by norm_num) (by norm_num) (by norm_num)).1]

theorem z24 : (zCert 24).pts.toList = zL 462 770 := by
  rw [(zBfs kZ24 (by norm_num) (by norm_num) (by norm_num)).1]

theorem z1 : (zCert 1).pts.toList = zL 1232 1232 := by
  rw [(zBfs kZ1 (by norm_num) (by norm_num) (by norm_num)).1]

theorem size_of_toList {a : Array ℕ} {l : List ℕ} (h : a.toList = l) : a.size = l.length := by
  rw [← h, Array.length_toList]

theorem mem_w7 {u : ℕ} : u ∈ wL 254 770 ↔ inOrb (IW 1) 12 1024 254 770 u = true :=
  mem_orb kWInv (by norm_num)

theorem mem_z24 {n : ℕ} : n ∈ zL 462 770 ↔ inOrb (IZ 1) 12 2464 462 770 n = true :=
  mem_orb kZInv (by norm_num)

theorem mem_z1 {n : ℕ} : n ∈ zL 1232 1232 ↔ inOrb (IZ 1) 12 2464 1232 1232 n = true :=
  mem_orb kZInv (by norm_num)

theorem lt_of_mem_w {o n u : ℕ} (hon : o + n ≤ 1024) (h : u ∈ wL o n) : u < 1024 := by
  obtain ⟨j, hj, rfl⟩ := mem_orbL.1 h
  exact (invTabOK_sound kWInv _ (by omega)).1

theorem lt_of_mem_z {o n x : ℕ} (hon : o + n ≤ 2464) (h : x ∈ zL o n) : x < 2464 := by
  obtain ⟨j, hj, rfl⟩ := mem_orbL.1 h
  exact (invTabOK_sound kZInv _ (by omega)).1

@[expose] def ltr (c : ℕ) : ℤ := if c = 0 then 1 else 2

theorem wordArr_size : ∀ w : List ℤ, (wordArr w).size = 3510
  | [] => by simp [wordArr, idArrN]
  | z :: w => by
    change (amulN (genArr z) (wordArr w)).size = 3510
    rw [amulN, Array.size_map, wordArr_size w]

theorem wordArr_get : ∀ (w : List ℤ) {x : ℕ}, x < 3510 →
    (wordArr w)[x]! = w.foldr (fun z y => (genArr z)[y]!) x
  | [], x, hx => by
    change (idArrN 3510)[x]! = x
    rw [idArrN, getElem!_pos _ x (by simpa using hx)]
    simp
  | z :: w, x, hx => by
    change (amulN (genArr z) (wordArr w))[x]! = _
    rw [amulN, getElem!_pos _ x (by rw [Array.size_map, wordArr_size]; exact hx), Array.getElem_map,
      ← getElem!_pos _ x (by rw [wordArr_size]; exact hx), wordArr_get w hx, List.foldr_cons]

theorem genArr_ltr {c y : ℕ} (hc : c < 2) (hy : y < 3510) :
    (genArr (ltr c))[y]! = fget (gen2 (IG.F 0) (IG.F 1) c) y 12 := by
  have e : genArr (ltr c) = indM22Gen c := by
    rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
    · simp [ltr, genArr, indA]
    · simp [ltr, genArr, indB]
  rw [e, gen2_get hc hy]

theorem trace_eq : ∀ (w : List ℕ), (∀ c ∈ w, c < 2) → ∀ {x : ℕ}, x < 3510 →
    (w.map ltr).foldr (fun z y => (genArr z)[y]!) x = wordT (IG.F 0) (IG.F 1) w x ∧
      wordT (IG.F 0) (IG.F 1) w x < 3510
  | [], _, x, hx => ⟨rfl, hx⟩
  | c :: w, hw, x, hx => by
    obtain ⟨ih, hlt⟩ := trace_eq w (fun c' hc' => hw c' (List.mem_cons_of_mem _ hc')) hx
    have hc := hw c List.mem_cons_self
    rw [List.map_cons, List.foldr_cons, ih, wordT_cons, genArr_ltr hc hlt]
    refine ⟨rfl, ?_⟩
    rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
    · exact (range_gen (g := 0) (by norm_num)).1 _ hlt
    · rw [gen2_ne one_ne_zero]
      exact (range_gen (g := 1) (by norm_num)).1 _ hlt

theorem sWord_eq : ∀ k < 4, sWord k = (sW[k]!).map ltr ∧ ∀ c ∈ sW[k]!, c < 2 := by
  decide +kernel

theorem s2Word_eq : ∀ k < 3, s2Word k = (s2W[k]!).map ltr ∧ ∀ c ∈ s2W[k]!, c < 2 := by
  decide +kernel

theorem sArrs_word {k x : ℕ} (hk : k < 4) (hx : x < 3510) :
    (sArrs[k]!)[x]! = wordT (IG.F 0) (IG.F 1) (sW[k]!) x := by
  have e : sArrs[k]! = wordArr (sWord k) := by
    rw [sArrs, getElem!_pos _ _ (by simp [hk])]
    simp
  obtain ⟨hw, hl⟩ := sWord_eq k hk
  rw [e, wordArr_get _ hx, hw, (trace_eq _ hl hx).1]

theorem s2Arrs_word {k x : ℕ} (hk : k < 3) (hx : x < 3510) :
    (s2Arrs[k]!)[x]! = wordT (IG.F 0) (IG.F 1) (s2W[k]!) x := by
  have e : s2Arrs[k]! = wordArr (s2Word k) := by
    rw [s2Arrs, getElem!_pos _ _ (by simp [hk])]
    simp
  obtain ⟨hw, hl⟩ := s2Word_eq k hk
  rw [e, wordArr_get _ hx, hw, (trace_eq _ hl hx).1]

theorem sArrs_size' : ∀ k < 4, (sArrs[k]!).size = 3510 := by
  intro k hk
  rw [sArrs, getElem!_pos _ _ (by simp [hk])]
  simp [wordArr_size]

theorem s2Arrs_size' : ∀ k < 3, (s2Arrs[k]!).size = 3510 := by
  intro k hk
  rw [s2Arrs, getElem!_pos _ _ (by simp [hk])]
  simp [wordArr_size]

theorem mem_getElem! {L : List (List ℕ)} {wd : List ℕ} (h : wd ∈ L) : ∃ k < L.length, L[k]! = wd := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 h
  exact ⟨k, hk, getElem!_pos L k hk⟩

theorem hex1 {s : String} {i : ℕ} (n : ℕ) (hi : i < n) :
    (hexTable3 1 i s)[0]! = (hexTable3 n 0 s)[i]! := by
  unfold hexTable3
  rw [getElem!_pos _ 0 (by simp), getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn,
    Array.getElem_ofFn]
  simp

theorem sig_get {i : ℕ} (hi : i < 1540) : (hexTable3 1 i indSigmaHex)[0]! = fget (ISg.F 0) i 12 := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound ISg.all 0 (by norm_num)
  rw [← ISg.eq, Nat.mul_zero] at h
  rw [hex1 1540 hi, h, CFSG.KS.Raw.Orb.unpack_get hi, pg_eq]

theorem tau_get {i : ℕ} (hi : i < 2464) : (hexTable3 1 i indTauHex)[0]! = fget (ITa.F 0) i 12 := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound ITa.all 0 (by norm_num)
  rw [← ITa.eq, Nat.mul_zero] at h
  rw [hex1 2464 hi, h, CFSG.KS.Raw.Orb.unpack_get hi, pg_eq]

theorem indSigma_eq :
    indSigma = (List.range 770).map fun i => (fget (ISg.F 0) i 12, fget (ISg.F 0) (770 + i) 12) := by
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  rw [sig_get (by omega), sig_get (by omega)]

theorem indTau_eq :
    indTau = (List.range 1232).map fun i => (fget (ITa.F 0) i 12, fget (ITa.F 0) (1232 + i) 12) := by
  refine List.map_congr_left fun i hi => ?_
  rw [List.mem_range] at hi
  rw [tau_get (by omega), tau_get (by omega)]

theorem key_table {H m S I N o n : ℕ} {P : ℕ} (hinv : invTabOK P 12 I 12 N = true) (hon : o + n ≤ N)
    (hk : keyOK H m S I 12 N o n = true) (hn : n ≤ m) (t : Array ℕ) (ht : t.size = N) :
    let l := (List.range m).map fun i => (fget H i 12, fget H (m + i) 12)
    (∀ i < m, fget H i 12 ∈ orbL P 12 o n ∧ (l.foldl (fun t p => t.set! p.1 p.2) t)[fget H i 12]! =
        fget H (m + i) 12 ∧ fget S (fget H i 12) 12 = fget H (m + i) 12) ∧
      ∀ u ∈ orbL P 12 o n, ∃ i < m, fget H i 12 = u := by
  intro l
  have hks := keyOK_sound hk
  have hmem : ∀ i < m, fget H i 12 ∈ orbL P 12 o n := fun i hi =>
    (mem_orb hinv hon).2 (hks i hi).1
  have hnd : (l.map Prod.fst).Nodup := by
    rw [List.map_map]
    exact nodup_keys fun i hi => (hks i (by omega)).2.2 hi
  refine ⟨fun i hi => ⟨hmem i hi, ?_, (hks i hi).2.1⟩, fun u hu => ?_⟩
  · refine foldl_set_get l t hnd (fget H i 12, fget H (m + i) 12)
      (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩) ?_
    rw [ht]
    exact (inOrb_iff.1 (hks i hi).1).1
  · have hsub : (List.range m).map (fun i => fget H i 12) ⊆ orbL P 12 o n := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      exact hmem i (List.mem_range.1 hi)
    have hu' := mem_of_subset_nodup hsub (by rw [List.map_map] at hnd; exact hnd)
      (by rw [orbL_length, List.length_map, List.length_range]; exact hn) hu
    obtain ⟨i, hi, e⟩ := List.mem_map.1 hu'
    exact ⟨i, List.mem_range.1 hi, e⟩

theorem sig_key :
    (∀ i < 770, fget (ISg.F 0) i 12 ∈ wL 254 770 ∧
      sigmaFun (fget (ISg.F 0) i 12) = fget (ISg.F 0) (770 + i) 12 ∧
      fget (IW 6) (fget (ISg.F 0) i 12) 12 = fget (ISg.F 0) (770 + i) 12) ∧
      ∀ u ∈ wL 254 770, ∃ i < 770, fget (ISg.F 0) i 12 = u := by
  have h := key_table kWInv (by norm_num) kSigK le_rfl (Array.replicate 1024 0) (by simp)
  rw [← indSigma_eq] at h
  exact h

theorem tau_key :
    (∀ i < 1232, fget (ITa.F 0) i 12 ∈ zL 1232 1232 ∧
      tauFun (fget (ITa.F 0) i 12) = fget (ITa.F 0) (1232 + i) 12 ∧
      fget (IZ 6) (fget (ITa.F 0) i 12) 12 = fget (ITa.F 0) (1232 + i) 12) ∧
      ∀ u ∈ zL 1232 1232, ∃ i < 1232, fget (ITa.F 0) i 12 = u := by
  have h := key_table kZInv (by norm_num) kTauK le_rfl (Array.replicate 2464 0) (by simp)
  rw [← indTau_eq] at h
  exact h

theorem sigma_tab {u : ℕ} (hu : u ∈ wL 254 770) : sigmaFun u = fget (IW 6) u 12 := by
  obtain ⟨i, hi, rfl⟩ := sig_key.2 u hu
  rw [(sig_key.1 i hi).2.1, (sig_key.1 i hi).2.2]

theorem tau_tab {n : ℕ} (hn : n ∈ zL 1232 1232) : tauFun n = fget (IZ 6) n 12 := by
  obtain ⟨i, hi, rfl⟩ := tau_key.2 n hn
  rw [(tau_key.1 i hi).2.1, (tau_key.1 i hi).2.2]

end CertificateChecks.KernelMonB.IndOrbGlue

end
