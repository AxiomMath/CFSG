module

public import CFSG.Certificates.Kernel.StdOdd.CentCheckSound
public import Certificates.Kernel.Misc.E6StdBridge
public import Certificates.Kernel.StdOdd.CentBridge

public section

namespace CFSG.KD.StdOdd.Cent

open CFSG.KC.StdOdd.Orbit CFSG.KC.StdOdd.Chain CFSG.KS.StdOdd.Orbit CFSG.KS.StdOdd.Chain
  CFSG.KD.StdOdd.Orbit CFSG.KC.Misc.E6Std CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel CFSG.Monster.Existence.StdOdd.Cert Matrix CFSG.KC.LQT.P

theorem nthN_eq_getD : ∀ (l : List ℕ) (i : ℕ), nthN l i = l.getD i 0
  | [], i => rfl
  | x :: l, 0 => rfl
  | x :: l, i + 1 => by rw [nthN_cons_succ, nthN_eq_getD l i]; rfl

theorem forall_zip_iff {P : ℕ → ℕ → Prop} : ∀ K : List (ℕ × ℕ),
    (∀ l < lenN (K.map Prod.fst), P (nthN (K.map Prod.fst) l) (nthN (K.map Prod.snd) l)) ↔
      ∀ q ∈ K, P q.1 q.2
  | [] => by simp [lenN]
  | q :: K => by
    rw [List.map_cons, List.map_cons, lenN_cons]
    constructor
    · intro h q' hq'
      rcases List.mem_cons.1 hq' with rfl | hq'
      · exact h 0 (by omega)
      · exact (forall_zip_iff K).1 (fun l hl => h (l + 1) (by omega)) q' hq'
    · intro h l hl
      cases l with
      | zero => exact h q List.mem_cons_self
      | succ l =>
        exact (forall_zip_iff K).2 (fun q' hq' => h q' (List.mem_cons_of_mem _ hq')) l (by omega)

theorem lenN_map_fst_snd (K : List (ℕ × ℕ)) : lenN (K.map Prod.fst) = lenN (K.map Prod.snd) := by
  rw [CFSG.KS.StdOdd.Chain.lenN_eq_length, CFSG.KS.StdOdd.Chain.lenN_eq_length, List.length_map, List.length_map]

theorem A_mem : toMat nativeAB.1 ∈ monAB := Submonoid.subset_closure (Set.mem_insert _ _)

theorem B_mem : toMat nativeAB.2 ∈ monAB :=
  Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem signed_mem (l : ℕ × Bool) : toMat (Native.signedMat nativeAB.1 nativeAB.2 l) ∈ monAB := by
  unfold Native.signedMat
  split_ifs
  · exact A_mem
  · exact B_mem
  · rw [toMat_mul]
    exact Submonoid.mul_mem _ B_mem B_mem

theorem wM_mem (w : List (ℕ × Bool)) : wM w ∈ monAB := by
  have key : ∀ (w : List (ℕ × Bool)) (P : Native.Mat), toMat P ∈ monAB →
      toMat (w.foldl (fun acc l => Native.mul acc (Native.signedMat nativeAB.1 nativeAB.2 l)) P) ∈
        monAB := by
    intro w
    induction w with
    | nil => exact fun P h => h
    | cons l w ih =>
      intro P h
      exact ih _ (by rw [toMat_mul]; exact Submonoid.mul_mem _ h (signed_mem l))
  exact key w _ (by rw [toMat_one]; exact Submonoid.one_mem _)

theorem rep_wM {A B : ℕ} (hA : Rep A (toMat nativeAB.1)) (hB : Rep B (toMat nativeAB.2))
    (w : List (ℕ × Bool)) : Rep (wordB A B w) (wM w) :=
  rep_wordB hA hB w

theorem getD_memS {M : Type*} [Monoid M] (S : Submonoid M) {arr : Array M}
    (h : ∀ x ∈ arr, x ∈ S) (i : ℕ) : arr.getD i 1 ∈ S := by
  rw [Array.getD_eq_getD_getElem?]
  cases e : arr[i]? with
  | none => exact S.one_mem
  | some y => exact h y (Array.mem_of_getElem? e)

theorem lineProdG_memS {M : Type*} [Monoid M] (S : Submonoid M) {vals : Array M}
    (hg : ∀ x ∈ vals, x ∈ S) (line : List ℕ) : lineProdG vals line ∈ S := by
  have h : ∀ (line : List ℕ) (acc : M), acc ∈ S →
      line.foldl (fun acc i => acc * vals.getD i 1) acc ∈ S := by
    intro line
    induction line with
    | nil => exact fun acc h => h
    | cons i line ih => exact fun acc hacc => ih _ (S.mul_mem hacc (getD_memS S hg i))
  exact h line 1 S.one_mem

theorem slpRunG_memS {M : Type*} [Monoid M] (S : Submonoid M) :
    ∀ (prog : List (List ℕ)) (gens : Array M), (∀ x ∈ gens, x ∈ S) →
      ∀ x ∈ slpRunG gens prog, x ∈ S
  | [], gens, hg => hg
  | line :: prog, gens, hg => by
    have e : slpRunG gens (line :: prog) = slpRunG (gens.push (lineProdG gens line)) prog := by
      rw [slpRunG, List.foldl_cons]
      rfl
    rw [e]
    refine slpRunG_memS S prog _ fun x hx => ?_
    rcases Array.mem_push.1 hx with hx | rfl
    · exact hg x hx
    · exact lineProdG_memS S hg line

@[expose] def gM (prog : List (List ℕ)) : Array M78 :=
  (Native.slpRun #[nativeAB.1, nativeAB.2] prog).map toMat

@[expose] def vM (prog : List (List ℕ)) (i : ℕ) : M78 := (gM prog).getD i 1

theorem gM_mem (prog : List (List ℕ)) : ∀ x ∈ gM prog, x ∈ monAB := by
  intro x hx
  rw [gM, toMat_slpRun] at hx
  refine slpRunG_memS monAB prog _ (fun y hy => ?_) x hx
  simp only [List.map_toArray, List.map_cons, List.map_nil, List.mem_toArray, List.mem_cons,
    List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  · exact A_mem
  · exact B_mem

theorem vM_mem (prog : List (List ℕ)) (i : ℕ) : vM prog i ∈ monAB :=
  getD_memS monAB (gM_mem prog) i

theorem rep_run2 {X Y : Native.Mat} {A B : ℕ} (hA : Rep A (toMat X)) (hB : Rep B (toMat Y))
    {V : List ℕ} {prog : List (List ℕ)} (h0 : Nat.beq (nthV V 0) A = true)
    (h1 : Nat.beq (nthV V 1) B = true) (hp : ∀ t < lenLL prog, slpLine V prog 2 t = true)
    (hn : Nat.beq (lenN V) (Nat.add 2 (lenLL prog)) = true) {i : ℕ} (hi : i < lenN V) :
    Rep (nthV V i) ((((Native.slpRun #[X, Y] prog).map toMat)).getD i 1) := by
  have hG : ∀ i < (#[X, Y] : Array Native.Mat).size,
      Rep (nthV V i) (toMat ((#[X, Y] : Array Native.Mat).getD i Native.one)) := by
    intro i hi
    change i < 2 at hi
    rcases i with _ | _ | i
    · exact rep_of_eq hA h0
    · exact rep_of_eq hB h1
    · omega
  rw [Nat.beq_eq] at hn
  have := rep_run hG hp i (by change i < 2 + lenLL prog; change lenN V = 2 + lenLL prog at hn; omega)
  rw [toMat_getD] at this
  exact this

theorem rep_vM {A B : ℕ} (hA : Rep A (toMat nativeAB.1)) (hB : Rep B (toMat nativeAB.2))
    {V : List ℕ} {prog : List (List ℕ)} (h0 : Nat.beq (nthV V 0) A = true)
    (h1 : Nat.beq (nthV V 1) B = true) (hp : ∀ t < lenLL prog, slpLine V prog 2 t = true)
    (hn : Nat.beq (lenN V) (Nat.add 2 (lenLL prog)) = true) {i : ℕ} (hi : i < lenN V) :
    Rep (nthV V i) (vM prog i) :=
  rep_run2 hA hB h0 h1 hp hn hi

theorem rep_line {V : List ℕ} {prog : List (List ℕ)}
    (hV : ∀ i < lenN V, Rep (nthV V i) (vM prog i)) (line : List ℕ)
    (hl : ∀ i ∈ line, i < lenN V) :
    Rep (lineB V line) (lineProdG (gM prog) line) :=
  rep_lineB V (gM prog) hV line hl

theorem rep_letters {V : List ℕ} {prog : List (List ℕ)}
    (hV : ∀ i < lenN V, Rep (nthV V i) (vM prog i)) (RI : List ℕ)
    (hRI : ∀ i ∈ RI, i < lenN V) :
    lenN (RI.map (nthV V)) = (RI.map (vM prog)).length ∧
      ∀ l < lenN (RI.map (nthV V)), Rep (nthN (RI.map (nthV V)) l) ((RI.map (vM prog)).getD l 0) := by
  refine ⟨by rw [CFSG.KS.StdOdd.Chain.lenN_eq_length, List.length_map, List.length_map], fun l hl => ?_⟩
  rw [CFSG.KS.StdOdd.Chain.lenN_eq_length, List.length_map] at hl
  rw [nthN_eq_getD, List.getD_eq_getElem _ _ (by simpa using hl),
    List.getD_eq_getElem _ _ (by simpa using hl), List.getElem_map, List.getElem_map]
  exact hV _ (hRI _ (List.getElem_mem _))

theorem monL_le {Ms : List M78} (h : ∀ M ∈ Ms, M ∈ monAB) : monL Ms ≤ monAB :=
  (Submonoid.closure_le).2 fun M hM => h M hM

theorem monL_AB : monL [toMat nativeAB.1, toMat nativeAB.2] ≤ monAB :=
  monL_le fun M hM => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
    rcases hM with rfl | rfl
    · exact A_mem
    · exact B_mem

theorem ptK_vecsPl (vs : List ℕ) {r : ℕ} (hr : r < vs.length) :
    ptK (vecsPl vs) r = vecK (nthN vs r) :=
  ptK_eq_vecK (ptB_vecsPl vs hr)

theorem vecK_e7 : vecK (2 ^ 14) = Pi.single 7 1 := by
  funext k
  simp only [vecK, Nat.testBit_two_pow]
  by_cases hk : (k : ℕ) = 7
  · have hk' : k = 7 := Fin.ext hk
    rw [hk', Pi.single_eq_same]
    simp [ofBits_true_false]
  · have hk' : k ≠ 7 := fun h => hk (by rw [h]; rfl)
    rw [Pi.single_eq_of_ne hk']
    simp only [show (14 = 2 * (k : ℕ)) = False by simp; omega,
      show (14 = 2 * (k : ℕ) + 1) = False by simp; omega, decide_false]
    exact ofBits_false

theorem fix_K {N : ℕ} {M : M78} (hN : Rep N M) {v : ℕ} (h : matB N *ᵥ vecB v = vecB v) :
    M *ᵥ vecK v = vecK v :=
  flat_inj (by rw [flat_mulVec, ← hN.2, ← matB_eq_decB, flat_vecK, h])

theorem map1_K {N u v : ℕ} {M : M78} (hN : Rep N M)
    (h : Nat.beq (neqV (mapRows N (vecsPl [u])) v 1) 0 = true) : M *ᵥ vecK u = vecK v := by
  have h1 := ptK_of_neqV (lenN_mapRows N _) h (i := 0) Nat.one_pos
  rw [ptK_mapRows (lenN_vecsPl _) hN, ptK_vecsPl [u] (by simp)] at h1
  exact h1

theorem comm_K {N X : ℕ} {M MX : M78} (hN : Rep N M) (hX : Rep X MX)
    (h : Nat.beq (mulB N X) (mulB X N) = true) : M * MX = MX * M :=
  (beq_iff_of_rep (rep_mulB hN hX) (rep_mulB hX hN)).1 h

theorem forest_K {FPn WN bw n D β : ℕ} {Ms : List ℕ} {Ks : List M78} (hlen : lenN Ms = Ks.length)
    (hrep : ∀ l < lenN Ms, Rep (nthN Ms l) (Ks.getD l 0)) (h : forestOK FPn WN bw n D Ms β = true) :
    (∀ i < n, ∀ i' < n, ptK (splitPl FPn bw n 156) i = ptK (splitPl FPn bw n 156) i' → i = i') ∧
      ∀ i < n, ∃ g ∈ monL Ks, g *ᵥ ptK (splitPl FPn bw n 156) i = vecK β := by
  unfold forestOK at h
  rw [forceLB_eq, andB_eq, Bool.and_eq_true] at h
  have hl := lenN_splitPl FPn bw n 156
  refine ⟨fun i hi i' hi' e => sort_inj hl h.1 i hi i' hi' (ptK_inj e), fun i hi => ?_⟩
  obtain ⟨V, hk, hV, hpt⟩ := walkK_sound _ _ hl h.2
  obtain ⟨g, hg, hge⟩ := walk_lift hlen hrep (stepsPl WN bw n D (lenN Ms)) i
  exact ⟨g, hg, (ptK_walk (hpt i) hge).symm.trans (ptK_of_neqV hV hk hi)⟩

theorem facts_ptK {PL : List ℕ} {A B n r : ℕ} (hA : Rep A (toMat nativeAB.1))
    (hB : Rep B (toMat nativeAB.2)) (h : OrbitBits PL A B n r) :
    (∀ i < n, ∀ j < n, ptK PL i = ptK PL j → i = j) ∧
      (∃ r < n, ptK PL r = Pi.single 7 1) ∧
      (∀ i < n, ∃ j < n, ptK PL j = toMat nativeAB.1 *ᵥ ptK PL i) ∧
      (∀ i < n, ∃ j < n, ptK PL j = toMat nativeAB.2 *ᵥ ptK PL i) ∧
      ∃ dep : ℕ → ℕ, (∀ i < n, dep i = 0 → ptK PL i = Pi.single 7 1) ∧
      (∀ i < n, 0 < dep i → ∃ j < n, dep j < dep i ∧
        (ptK PL i = toMat nativeAB.1 *ᵥ ptK PL j ∨ ptK PL i = toMat nativeAB.2 *ᵥ ptK PL j ∨
          ptK PL j = toMat nativeAB.2 *ᵥ ptK PL i)) := by
  obtain ⟨dep, h0, hs⟩ := h.conn
  have hroot := ptK_root h.root
  refine ⟨fun i hi j hj e => h.inj i hi j hj (by rw [← flat_ptK, ← flat_ptK, e]),
    ⟨r, h.root_lt, hroot⟩, fun i hi => ?_, fun i hi => ?_, dep, fun i hi hd => ?_, fun i hi hd => ?_⟩
  · obtain ⟨j, hj, e⟩ := h.closA i hi
    exact ⟨j, hj, (step_iff hA i j).1 e⟩
  · obtain ⟨j, hj, e⟩ := h.closB i hi
    exact ⟨j, hj, (step_iff hB i j).1 e⟩
  · rw [h0 i hi hd, hroot]
  · obtain ⟨j, hj, hlt, e⟩ := hs i hi hd
    refine ⟨j, hj, hlt, ?_⟩
    rcases e with e | e | e
    · exact Or.inl ((step_iff hA j i).1 e)
    · exact Or.inr (Or.inl ((step_iff hB j i).1 e))
    · exact Or.inr (Or.inr ((step_iff hB i j).1 e))

theorem card_filter_eq_sum {P : ℕ → Prop} [DecidablePred P] (m : ℕ) :
    ((Finset.range m).filter P).card = ∑ i ∈ Finset.range m, if P i then 1 else 0 := by
  rw [Finset.card_filter]

theorem card_chunk_step (P : ℕ → Prop) [DecidablePred P] (a b : ℕ) :
    ((Finset.range (a + b)).filter P).card =
      ((Finset.range a).filter P).card + ((Finset.range b).filter fun i => P (a + i)).card := by
  rw [card_filter_eq_sum, card_filter_eq_sum, card_filter_eq_sum, Finset.sum_range_add]

theorem card_filter_chunks (P : ℕ → Prop) [DecidablePred P] (C n Q : ℕ) (hQ : n ≤ Q * C) :
    ((Finset.range n).filter P).card =
      ∑ q ∈ Finset.range Q, ((Finset.range (min C (n - q * C))).filter fun i => P (q * C + i)).card := by
  have key : ∀ Q, ((Finset.range (min n (Q * C))).filter P).card =
      ∑ q ∈ Finset.range Q, ((Finset.range (min C (n - q * C))).filter fun i => P (q * C + i)).card := by
    intro Q
    induction Q with
    | zero => rw [Nat.zero_mul, Nat.min_zero, Finset.sum_range_zero, Finset.range_zero,
        Finset.filter_empty, Finset.card_empty]
    | succ Q ih =>
      rw [Finset.sum_range_succ, ← ih, Nat.add_mul, Nat.one_mul]
      generalize Q * C = a
      by_cases hn : n ≤ a
      · rw [show min n (a + C) = min n a by omega, Nat.sub_eq_zero_of_le hn, Nat.min_zero,
          Finset.range_zero, Finset.filter_empty, Finset.card_empty, Nat.add_zero]
      · have e1 : min n (a + C) = a + min C (n - a) := by omega
        rw [e1, card_chunk_step, show min n a = a by omega]
  rw [← key Q, min_eq_left hQ]

end CFSG.KD.StdOdd.Cent

end
