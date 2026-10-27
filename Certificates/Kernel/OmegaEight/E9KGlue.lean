module

public import Certificates.Kernel.OmegaEight.E9KChecks
public import Certificates.Kernel.OmegaEight.Aut
public import CFSG.Certificates.Kernel.PGrpMul
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Local
import CFSG.Certificates.Kernel.BfsPinBaseSound
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.BfsPinSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.E9K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum CFSG.KC.PGrp
open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Co2 CFSG.RankThree.Native CFSG.Monster.B.Fischer
open CFSG.RankThree.PartTwo.Sec4.Item434O8pE9
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 (posWord getElem!_map')
open CertificateChecks.KernelO8

theorem hw9 : szOK 360 9 = true := by quickRfl

theorem hn : (360 : ℕ) < 2 ^ 32 := by norm_num

theorem psLt : ∀ p ∈ ps, p < 360 := by decide

theorem n_eq : o8pE9.n = 360 := rfl

theorem qKeys_eq : o8pE9.qKeys = ps := rfl

theorem dKeys_eq : o8pE9.dKeys = ps := rfl

theorem nums' : E9Q.ng = 3 ∧ E9Q.N = 243 ∧ E9D.ng = 4 ∧ E9D.N = 81 := by
  have h := nums
  simp only [Bool.and_eq_true] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1.1.1, Nat.eq_of_beq_eq_true h.1.1.2,
    Nat.eq_of_beq_eq_true h.1.2, Nat.eq_of_beq_eq_true h.2⟩

theorem idKey_eq : CFSG.KC.BfsPin.keyK 360 9 ps (pidn 360 9) = idKey := Nat.eq_of_beq_eq_true idK

theorem permId : permB 360 9 (pidn 360 9) = true := permB_of_pp (PP.id hw9)

theorem strictB_eq' (y : ℕ) (k : ℕ → Bool) : strictB y k = k y := by cases y <;> rfl

theorem map_get {W : Array (List ℕ)} {f : List ℕ → ℕ} {G : ℕ → ℕ} {m : ℕ}
    (h : W.toList.map f = (List.range m).map G) : W.size = m ∧ ∀ k < m, f W[k]! = G k := by
  have hs : W.size = m := by simpa using congrArg List.length h
  refine ⟨hs, fun k hk => ?_⟩
  have hk' : k < (W.toList.map f).length := by simp [hs, hk]
  have e := List.getElem_of_eq h hk'
  rw [List.getElem_map, List.getElem_map, List.getElem_range, Array.getElem_toList] at e
  rw [getElem!_pos W k (by omega)]
  exact e

theorem letters_of_toList {W : Array (List ℕ)} {m : ℕ}
    (h : (W.toList.all fun w => w.all fun l => decide (l < m)) = true) :
    ∀ k < W.size, ∀ l ∈ W[k]!, l < m := by
  intro k hk l hl
  rw [List.all_eq_true] at h
  have h1 := h W[k]! (by rw [getElem!_pos W k hk]; exact Array.getElem_mem_toList hk)
  simpa using List.all_eq_true.1 h1 l hl

theorem permS : ∀ j < 8, permB 360 9 (OmP.S j) = true := allN_spec perm

theorem pgS : o8pE9.pg.size = 8 ∧ ∀ j < 8, o8pE9.pg[j]! = unpack 360 9 (OmP.S j) := genOm

theorem qgen {k : ℕ} (hk : k < 3) :
    (qGens o8pE9)[k]! = unpack 360 9 (E9Q.G k) ∧ permB 360 9 (E9Q.G k) = true := by
  have hk' : k < o8pE9.qW.size := by rw [(map_get wordsQ).1]; exact hk
  obtain ⟨e, p⟩ := posWord_unpack hw9 pgS.2 permS (letters_of_toList lettersQ k hk')
  rw [(map_get wordsQ).2 k hk] at e p
  refine ⟨?_, p⟩
  rw [qGens, getElem!_map' _ _ hk', n_eq]
  exact e

theorem qsize : (qGens o8pE9).size = 3 := by rw [qGens, Array.size_map, (map_get wordsQ).1]

theorem dgen {k : ℕ} (hk : k < 4) :
    (dGens o8pE9)[k]! = unpack 360 9 (E9D.G k) ∧ permB 360 9 (E9D.G k) = true := by
  have hk' : k < o8pE9.dW.size := by rw [(map_get wordsD).1]; exact hk
  obtain ⟨e, p⟩ := posWord_unpack hw9 (fun l hl => (qgen hl).1) (fun l hl => (qgen hl).2)
    (letters_of_toList lettersD k hk')
  rw [(map_get wordsD).2 k hk] at e p
  refine ⟨?_, p⟩
  rw [dGens, getElem!_map' _ _ hk', n_eq]
  exact e

theorem dsize : (dGens o8pE9).size = 4 := by rw [dGens, Array.size_map, (map_get wordsD).1]

theorem hgen {k : ℕ} (hk : k < 4) :
    (hArrs o8pE9)[k]! = unpack 360 9 (E9H k) ∧ permB 360 9 (E9H k) = true := by
  have hk' : k < o8pE9.hW.size := by rw [(map_get wordsH).1]; exact hk
  obtain ⟨e, p⟩ := posWord_unpack hw9 pgS.2 permS (letters_of_toList lettersH k hk')
  rw [(map_get wordsH).2 k hk] at e p
  refine ⟨?_, p⟩
  rw [hArrs, getElem!_map' _ _ hk', n_eq]
  exact e

theorem hsize : (hArrs o8pE9).size = 4 := by rw [hArrs, Array.size_map, (map_get wordsH).1]

theorem q_gens : (qGens o8pE9).size = E9Q.ng ∧
    ∀ k < E9Q.ng, (qGens o8pE9)[k]! = unpack 360 9 (E9Q.G k) := by
  rw [nums'.1]
  exact ⟨qsize, fun k hk => (qgen hk).1⟩

theorem q_perm : ∀ k < E9Q.ng,
    permOK 360 9 (mask 9) (360 * 9) (E9Q.G k) (pinvS 360 9 (mask 9) (E9Q.G k)) = true := by
  rw [nums'.1]
  exact fun k hk => (qgen hk).2

theorem d_gens : (dGens o8pE9).size = E9D.ng ∧
    ∀ k < E9D.ng, (dGens o8pE9)[k]! = unpack 360 9 (E9D.G k) := by
  rw [nums'.2.2.1]
  exact ⟨dsize, fun k hk => (dgen hk).1⟩

theorem d_perm : ∀ k < E9D.ng,
    permOK 360 9 (mask 9) (360 * 9) (E9D.G k) (pinvS 360 9 (mask 9) (E9D.G k)) = true := by
  rw [nums'.2.2.1]
  exact fun k hk => (dgen hk).2

theorem q_pts : (qCert o8pE9).pts = Array.ofFn (n := E9Q.N) fun i => unpack 360 9 (E9Q.T i.val) := by
  unfold qCert
  rw [n_eq, qKeys_eq]
  exact enumBfs_pts_base q_gens.1 q_gens.2 E9Q.ok psLt keysQ (by rw [nums'.2.1]; decide)

theorem q_enum : enumOK 360 (qGens o8pE9) ps (qCert o8pE9) = true := by
  unfold qCert
  rw [n_eq, qKeys_eq]
  exact enumOK_of_bfsK_base q_gens.1 q_gens.2 q_perm E9Q.ok psLt keysQ (by rw [nums'.2.1]; decide)

theorem d_pts : (dCert o8pE9).pts = Array.ofFn (n := E9D.N) fun i => unpack 360 9 (E9D.T i.val) := by
  unfold dCert
  rw [n_eq, dKeys_eq]
  exact enumBfs_pts_base d_gens.1 d_gens.2 E9D.ok psLt keysD (by rw [nums'.2.2.2]; decide)

theorem d_enum : enumOK 360 (dGens o8pE9) ps (dCert o8pE9) = true := by
  unfold dCert
  rw [n_eq, dKeys_eq]
  exact enumOK_of_bfsK_base d_gens.1 d_gens.2 d_perm E9D.ok psLt keysD (by rw [nums'.2.2.2]; decide)

theorem q_size : (qCert o8pE9).pts.size = 243 := by rw [q_pts, Array.size_ofFn, nums'.2.1]

theorem d_size : (dCert o8pE9).pts.size = 81 := by rw [d_pts, Array.size_ofFn, nums'.2.2.2]

theorem q_get : ∀ i < 243, (qCert o8pE9).pts[i]! = unpack 360 9 (E9Q.T i) := fun i hi => by
  rw [q_pts, getElem!_pos _ i (by rw [Array.size_ofFn, nums'.2.1]; exact hi), Array.getElem_ofFn]

theorem d_get : ∀ i < 81, (dCert o8pE9).pts[i]! = unpack 360 9 (E9D.T i) := fun i hi => by
  rw [d_pts, getElem!_pos _ i (by rw [Array.size_ofFn, nums'.2.2.2]; exact hi), Array.getElem_ofFn]

theorem permQ {i : ℕ} (hi : i < 243) : permB 360 9 (E9Q.T i) = true :=
  permB_of_pp (PP_pts E9Q.ok q_perm i (by rw [nums'.2.1]; exact hi))

theorem permD {i : ℕ} (hi : i < 81) : permB 360 9 (E9D.T i) = true :=
  permB_of_pp (PP_pts E9D.ok d_perm i (by rw [nums'.2.2.2]; exact hi))

theorem memQ {i : ℕ} (hi : i < 243) :
    permOfArr 360 (unpack 360 9 (E9Q.T i)) ∈ Subgroup.closure (permsA 360 (qGens o8pE9)) :=
  mem_of_pt hw9 psLt q_enum q_size q_get hi

theorem keyC3_eq (P : ℕ) :
    CFSG.KC.BfsPin.keyK 360 9 ps (pcomp 360 9 (mask 9) P (pcomp 360 9 (mask 9) P P)) =
      keyC3 P := by
  rw [keyK_pcomp hn P _ psLt]
  have h0 := PF.pg_pcomp (w := 9) (p := P) (q := P) hn (show (0 : ℕ) < 360 by norm_num)
  have h1 := PF.pg_pcomp (w := 9) (p := P) (q := P) hn (show (1 : ℕ) < 360 by norm_num)
  have h2 := PF.pg_pcomp (w := 9) (p := P) (q := P) hn (show (2 : ℕ) < 360 by norm_num)
  simp only [keyCK, keyC3, ps]
  rw [h0, h1, h2]

theorem cb_eq {a : ℕ} (ha : a < 243) : (cubeOne 360 (qCert o8pE9))[a]! = cubeK a := by
  have pa := permQ ha
  have p2 := permB_pcomp hw9 pa pa
  have p3 := permB_pcomp hw9 pa p2
  unfold cubeOne
  rw [getElem!_map' (qCert o8pE9).pts _ (k := a) (by rw [q_size]; exact ha)]
  rw [q_get a ha, comp_unpack' hw9 pa pa, comp_unpack' hw9 pa p2, idA_eq hw9,
    eqA_unpack' hw9 p3 permId,
    beq_iff_keyK hw9 psLt q_enum p3 permId
      (mem_mul hw9 pa p2 (memQ ha) (mem_mul hw9 pa pa (memQ ha) (memQ ha))) (mem_id hw9),
    keyC3_eq, idKey_eq]
  rfl

theorem one_eq {a : ℕ} (ha : a < 243) : eqA 360 (qCert o8pE9).pts[a]! (idA 360) = oneK a := by
  rw [q_get a ha, idA_eq hw9, eqA_unpack' hw9 (permQ ha) permId,
    beq_iff_keyK hw9 psLt q_enum (permQ ha) permId (memQ ha) (mem_id hw9), idKey_eq]
  rfl

theorem comm_eq {a b : ℕ} (ha : a < 243) (hb : b < 243) :
    eqA 360 (compA 360 (qCert o8pE9).pts[a]! (qCert o8pE9).pts[b]!)
        (compA 360 (qCert o8pE9).pts[b]! (qCert o8pE9).pts[a]!) =
      Nat.beq (keyCK 360 9 ps (E9Q.T a) (E9Q.T b)) (keyCK 360 9 ps (E9Q.T b) (E9Q.T a)) := by
  rw [q_get a ha, q_get b hb]
  exact eqA_keyCK hw9 psLt q_enum (permQ ha) (permQ hb) (permQ hb) (permQ ha) (memQ ha) (memQ hb)
    (memQ hb) (memQ ha)

theorem sq_eq {a b : ℕ} (ha : a < 243) (hb : b < 243) :
    eqA 360 (qCert o8pE9).pts[b]! (compA 360 (qCert o8pE9).pts[a]! (qCert o8pE9).pts[a]!) =
      Nat.beq (CFSG.KC.BfsPin.keyK 360 9 ps (E9Q.T b)) (keyCK 360 9 ps (E9Q.T a) (E9Q.T a)) := by
  have pa := permQ ha
  rw [q_get a ha, q_get b hb, comp_unpack' hw9 pa pa,
    eqA_unpack' hw9 (permQ hb) (permB_pcomp hw9 pa pa),
    beq_iff_keyK hw9 psLt q_enum (permQ hb) (permB_pcomp hw9 pa pa) (memQ hb)
      (mem_mul hw9 pa pa (memQ ha) (memQ ha)),
    keyK_pcomp hn _ _ psLt]

theorem self_eq {a : ℕ} (ha : a < 243) :
    eqA 360 (qCert o8pE9).pts[a]! (qCert o8pE9).pts[a]! = true := by
  rw [q_get a ha]
  have r := rep_of_validA (validA_unpack (permQ ha))
  exact (eqA_iff r r).2 rfl

theorem cov_eq {i a : ℕ} (hi : i < 4) (ha : a < 243) (hc : cvK i a = true) :
    (((hArrs o8pE9).map fun h => covRow 360 (dCert o8pE9) h (qCert o8pE9))[i]!)[a]! = true := by
  have hcw := allN_spec cw (243 * i + a) (by omega)
  have e1 : Nat.div (243 * i + a) 243 = i := by
    change (243 * i + a) / 243 = i
    omega
  have e2 : Nat.mod (243 * i + a) 243 = a := by
    change (243 * i + a) % 243 = a
    omega
  unfold cwOK at hcw
  simp only [strictB_eq'] at hcw
  rw [e1, e2] at hcw
  change Nat.blt 0 (E9CW (243 * i + a)) = true at hc
  generalize E9CW (243 * i + a) = j at hcw hc
  have hb0 : Nat.beq j 0 = false := by
    cases j with
    | zero => exact absurd hc (by decide)
    | succ k => rfl
  rw [hb0, Bool.false_or, Bool.and_eq_true] at hcw
  have hj : j - 1 < 81 := by
    have := Nat.le_of_ble_eq_true hcw.1
    omega
  have hmul := Nat.eq_of_beq_eq_true hcw.2
  obtain ⟨eh, ph⟩ := hgen hi
  rw [getElem!_map' (hArrs o8pE9) _ (k := i) (by rw [hsize]; exact hi)]
  unfold covRow
  rw [getElem!_map' (qCert o8pE9).pts _ (k := a) (by rw [q_size]; exact ha)]
  rw [eh, q_get a ha, List.any_eq_true]
  have hj' : j - 1 < (dCert o8pE9).pts.size := by rw [d_size]; exact hj
  refine ⟨(dCert o8pE9).pts[j - 1]!, ?_, ?_⟩
  · rw [getElem!_pos (dCert o8pE9).pts (j - 1) hj']
    exact Array.getElem_mem_toList hj'
  · rw [d_get _ hj]
    have vH := validA_unpack ph
    have vQ := validA_unpack (permQ ha)
    have vD := validA_unpack (permD hj)
    have e3 : compA 360 (unpack 360 9 (E9H i)) (unpack 360 9 (E9Q.T a)) =
        compA 360 (unpack 360 9 (E9D.T (j - 1))) (unpack 360 9 (E9H i)) := by
      rw [comp_unpack' hw9 ph (permQ ha), comp_unpack' hw9 (permD hj) ph]
      exact congrArg _ hmul
    have r1 := rep_compA (rep_of_validA vH) (rep_of_validA vQ)
    have r2 := rep_compA (rep_of_validA vD) (rep_of_validA vH)
    rw [e3] at r1
    have e4 := r1.unique r2
    refine (eqA_iff (rep_conjA vH (rep_of_validA vQ)) (rep_of_validA vD)).2 ?_
    rw [e4, mul_inv_cancel_right]

theorem pair_eq {a b : ℕ} (ha : a < 243) (hb : b < 243) :
    CFSG.RankThree.PartTwo.Sec4.Item434O8pE9.pairOK 360 (qCert o8pE9)
      (cubeOne 360 (qCert o8pE9))
      ((hArrs o8pE9).map fun h => covRow 360 (dCert o8pE9) h (qCert o8pE9)) a b = true := by
  have h := allN_spec (allN_spec pairs a ha) b hb
  have hcs : ((hArrs o8pE9).map fun h => covRow 360 (dCert o8pE9) h (qCert o8pE9)).size = 4 := by
    rw [Array.size_map, hsize]
  unfold pairK at h
  unfold CFSG.RankThree.PartTwo.Sec4.Item434O8pE9.pairOK
  rw [cb_eq ha, cb_eq hb, one_eq ha, one_eq hb, comm_eq ha hb, sq_eq ha hb, hcs]
  simp only [Bool.or_eq_true] at h ⊢
  have hcov : ∀ i < 4, cvK i a = true → cvK i b = true →
      ((List.range 4).any fun i =>
        (((hArrs o8pE9).map fun h => covRow 360 (dCert o8pE9) h (qCert o8pE9))[i]!)[a]! &&
        (((hArrs o8pE9).map fun h => covRow 360 (dCert o8pE9) h (qCert o8pE9))[i]!)[b]!) =
        true := fun i hi h1 h2 => by
    rw [List.any_eq_true]
    exact ⟨i, List.mem_range.2 hi, by rw [cov_eq hi ha h1, cov_eq hi hb h2]; rfl⟩
  rcases h with ((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
  · have e := Nat.eq_of_beq_eq_true h
    subst e
    exact Or.inl (Or.inl (Or.inl (Or.inr (self_eq ha))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · rw [Bool.and_eq_true] at h
    exact Or.inr (hcov 0 (by norm_num) h.1 h.2)
  · rw [Bool.and_eq_true] at h
    exact Or.inr (hcov 1 (by norm_num) h.1 h.2)
  · rw [Bool.and_eq_true] at h
    exact Or.inr (hcov 2 (by norm_num) h.1 h.2)
  · rw [Bool.and_eq_true] at h
    exact Or.inr (hcov 3 (by norm_num) h.1 h.2)

theorem elem' :
    CFSG.RankThree.PartTwo.Sec4.Item434SporE81.elemAbOK 360 (dGens o8pE9) = true := by
  unfold CFSG.RankThree.PartTwo.Sec4.Item434SporE81.elemAbOK
  rw [allLt_iff]
  intro a ha
  rw [dsize] at ha
  have hr := allN_spec elem a ha
  rw [Bool.and_eq_true] at hr ⊢
  obtain ⟨ea, pa⟩ := dgen ha
  refine ⟨?_, ?_⟩
  · rw [ea, comp_unpack' hw9 pa pa, comp_unpack' hw9 pa (permB_pcomp hw9 pa pa), idA_eq hw9,
      eqA_unpack' hw9 (permB_pcomp hw9 pa (permB_pcomp hw9 pa pa)) permId]
    exact hr.1
  · rw [allLt_iff]
    intro b hb
    rw [dsize] at hb
    obtain ⟨eb, pb⟩ := dgen hb
    rw [ea, eb, comp_unpack' hw9 pa pb, comp_unpack' hw9 pb pa,
      eqA_unpack' hw9 (permB_pcomp hw9 pa pb) (permB_pcomp hw9 pb pa)]
    exact allN_spec hr.2 b hb

theorem e9Check_true : e9Check o8pE9 = true := by
  unfold e9Check e9Check'
  rw [n_eq, qKeys_eq, dKeys_eq]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, rfl⟩, ?_⟩, ?_⟩, ?_⟩, q_enum⟩, ?_⟩, d_enum⟩, ?_⟩, elem'⟩, ?_⟩, ?_⟩
  · rw [allLt_iff, pgS.1]
    intro k hk
    rw [pgS.2 k hk]
    exact validA_unpack (permS k hk)
  · rw [← Array.all_toList, pgS.1]
    exact lettersQ
  · rw [← Array.all_toList, pgS.1]
    exact lettersH
  · rw [← Array.all_toList, qsize]
    exact lettersD
  · rw [q_size]
    rfl
  · rw [d_size]
    rfl
  · rw [allLt_iff, hsize]
    intro k hk
    rw [(hgen hk).1]
    exact validA_unpack (hgen hk).2
  · rw [allLt_iff, q_size]
    intro a ha
    rw [allLt_iff]
    intro b hb
    exact pair_eq ha hb

end CertificateChecks.KernelO8.E9K

end
