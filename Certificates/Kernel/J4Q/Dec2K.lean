module

public import Certificates.Kernel.J4Q.X0OrbOk
public import Certificates.Kernel.J4Q.C4014
public import Certificates.Kernel.J4Q.LocVec
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2Native
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.Loop CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2A CFSG.Sporadic.J4.QT2 CFSG.QuasithinUnique.A5.Dec2

@[expose] noncomputable def anyR (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun i ih => orB ih (f i)) n

@[expose] noncomputable def d2P (Gs : List Nat) : List (Nat × Nat) :=
  [(0, getN one Gs 0), (1, getN one Gs 1), (2, getN one Gs 2), (3, getN one Gs 3)]

@[expose] noncomputable def d2E (Gs : List Nat) (m : Nat) : Nat := selPK c rm (d2P Gs) m one

@[expose] noncomputable def d2Es (Gs : List Nat) : List Nat := smapK (d2E Gs) (rangeK 16)

@[expose] noncomputable def d2X : Nat := getN one XG 0

@[expose] noncomputable def d2GrpK (Gs : List Nat) : Bool :=
  (fun Es => andB (distinctK Es) (andB (Nat.beq (getN one Es 0) one)
    (andB (allR 16 fun m => allR 16 fun m' =>
        Nat.beq (mulJ c rm (getN one Es m) (getN one Es m')) (getN one Es (Nat.xor m m')))
      (allR 4 fun k => Nat.beq (getN one Gs k) (getN one Es (Nat.pow 2 k)))))) (d2Es Gs)

@[expose] noncomputable def d2NormK (Gs : List Nat) : Bool :=
  (fun Es => andB (allR 16 fun m => anyR 16 fun m' =>
      Nat.beq (mulJ c rm d2X (getN one Es m)) (mulJ c rm (getN one Es m') d2X))
    (allR 15 fun m => notB (Nat.beq (mulJ c rm d2X (getN one Es (Nat.succ m)))
      (mulJ c rm (getN one Es (Nat.succ m)) d2X)))) (d2Es Gs)

@[expose] noncomputable def d2NotOrd (M r : Nat) : Bool :=
  notB (andB (notB (Nat.beq M one)) (Nat.beq (powJ c rm one M r) one))

@[expose] noncomputable def d2K0At (Gs : List Nat) (q : Nat) : Bool :=
  (fun M => orB (notB (allR 4 fun k => Nat.beq (mulJ c rm M (getN one Gs k)) (mulJ c rm (getN one Gs k) M)))
    (andB (andB (d2NotOrd M 3) (d2NotOrd M 7)) (d2NotOrd M 23))) (CFSG.KD.X0O.MSF q)

@[expose] noncomputable def d2K0K (Gs : List Nat) (c : Nat) : Bool :=
  allR 64 fun j => d2K0At Gs (Nat.add (Nat.mul 64 c) j)

@[expose] noncomputable def d2NR : Nat :=
  mulJ c rm (mulJ c rm (wordJ c rm one G5 G5i nWordU) (etaK c rm one Us nMask)) (wordJ c rm one G5 G5i nWordV)

@[expose] noncomputable def d2NK (Gs : List Nat) (q i j : Nat) : Bool :=
  (fun Es n => andB (allR 16 fun m => anyR 16 fun m' =>
      Nat.beq (mulJ c rm n (getN one Es m)) (mulJ c rm (getN one Es m') n))
    (andB (orB (Nat.beq j 2) (orB (Nat.beq j 3) (Nat.beq j 4)))
      (andB (Nat.blt q 6720) (andB (Nat.blt i 3)
        (Nat.beq (mulJ c rm n d2X) (mulJ c rm (powJ c rm one d2X j) n))))))
    (d2Es Gs) (mulJ c rm (CFSG.KD.X0O.MSF q) (powJ c rm one d2NR (Nat.succ i)))

@[expose] noncomputable def d2WK (Gs : List Nat) (Q QI : Nat) : Bool :=
  (fun Es => andB (andB (canonJ pad QI) (Nat.beq (mulJ c rm Q QI) one))
    (andB (allR 16 fun m => Nat.beq (mulJ c rm Q (getN one Es m)) (mulJ c rm (getN one Es m) Q))
      (distinctK (List.append (smapK (fun m => mulJ c rm (mulJ c rm (getN one Es m) d2X) (getN one Es m))
        (rangeK 16)) [mulJ c rm (mulJ c rm Q d2X) QI])))) (d2Es Gs)

theorem anyR_eq (f : Nat → Bool) : ∀ n, anyR n f = (List.range n).any f
  | 0 => rfl
  | n + 1 => by
    change orB (anyR n f) (f n) = _
    rw [anyR_eq f n, orB_eq'', List.range_succ, List.any_append, List.any_cons, List.any_nil,
      Bool.or_false]

theorem any_range_congr {f g : Nat → Bool} : ∀ {n : Nat}, (∀ i < n, f i = g i) →
    (List.range n).any f = (List.range n).any g
  | 0, _ => rfl
  | n + 1, h => by
    rw [List.range_succ, List.any_append, List.any_append,
      any_range_congr fun i hi => h i (Nat.lt_succ_of_lt hi), List.any_cons, List.any_cons,
      h n (Nat.lt_succ_self n), List.any_nil, List.any_nil]

theorem getN_eq_getD (d : Nat) : ∀ (l : List Nat) (k : Nat), getN d l k = l.getD k d
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, k + 1 => getN_eq_getD d l k

theorem getN_map_range (d : Nat) (f : Nat → Nat) {n k : Nat} (hk : k < n) :
    getN d ((List.range n).map f) k = f k := by
  rw [getN_eq_getD, List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map, List.getElem_range]

theorem d2Es_get (Gs : List Nat) {m : Nat} (hm : m < 16) : getN one (d2Es Gs) m = d2E Gs m := by
  rw [d2Es, smapK_eq, rangeK_eq, getN_map_range _ _ hm]

theorem mats_get {L : Array (Array V2)} {MS : Nat → Nat} {n : Nat}
    (hmap : L.toList.map encR = (List.range n).map MS) (hwf : ∀ X ∈ L.toList, WfA X) {q : Nat}
    (hq : q < n) : WfA (L[q]!) ∧ encR (L[q]!) = MS q := by
  have hl : L.size = n := by
    have := congrArg List.length hmap
    simpa using this
  have hq' : q < L.size := by omega
  rw [getElem!_pos L q hq']
  have hmem : L[q] ∈ L.toList := by
    rw [← Array.getElem_toList]
    exact List.getElem_mem _
  refine ⟨hwf _ hmem, ?_⟩
  have := congrArg (fun l => l[q]?) hmap
  simp only [List.getElem?_map, List.getElem?_range hq, Option.map_some] at this
  rw [← Array.getElem_toList, ← Option.some_inj]
  rw [← this]
  simp [hq']

variable (ws : List (List Int)) (Gs : List Nat)
  (hG : ∀ k < 4, WfA (wR (ws.getD k [])) ∧ encR (wR (ws.getD k [])) = getN one Gs k)

include hG in
theorem eW_enc (m : Nat) : WfA (wR (eW ws m)) ∧ encR (wR (eW ws m)) = d2E Gs m := by
  have hsel : wR (eW ws m) = selRows (fun k => wR (ws.getD k [])) m (List.range 4) (idRows ()) := by
    unfold eW wR
    rw [wordRows_flatMap g5_wf g5i_wf]
    exact foldl_sel g5_wf g5i_wf (fun k => ws.getD k []) m _ _ wf_idRows
  have hP : (d2P Gs).map Prod.fst = List.range 4 := rfl
  have := enc_selRows hK (fun k => wR (ws.getD k [])) m (d2P Gs) (by
    intro p hp
    simp only [d2P, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact hG 0 (by decide)
    · exact hG 1 (by decide)
    · exact hG 2 (by decide)
    · exact hG 3 (by decide)) (idRows ()) wf_idRows
  rw [hP, enc_idRows hK] at this
  rw [hsel]
  exact this

include hG in
theorem eTab_enc {m : Nat} (hm : m < 16) : WfA ((eTab ws)[m]!) ∧ encR ((eTab ws)[m]!) = getN one (d2Es Gs) m := by
  have : (eTab ws)[m]! = wR (eW ws m) := by
    simp [eTab, hm]
  rw [this, d2Es_get Gs hm]
  exact eW_enc ws Gs hG m

theorem xR_enc : WfA xR ∧ encR xR = d2X := x0Gen_enc (i := 0) (by decide)

theorem anyR_spec {n : Nat} {f : Nat → Bool} (h : anyR n f = true) : ∃ i < n, f i = true := by
  rw [anyR_eq, List.any_eq_true] at h
  obtain ⟨i, hi, h⟩ := h
  exact ⟨i, List.mem_range.1 hi, h⟩

theorem xor_lt16 {m m' : Nat} (hm : m < 16) (hm' : m' < 16) : m ^^^ m' < 16 :=
  Nat.xor_lt_two_pow (n := 4) hm hm'

theorem pow2_lt16 {k : Nat} (hk : k < 4) : 2 ^ k < 16 := by
  rcases k with _ | _ | _ | _ | k
  all_goals first | decide | omega

theorem es_map (hm : ∀ m < 16, encR ((eTab ws)[m]!) = getN one (d2Es Gs) m) :
    ((List.range 16).map fun m => (eTab ws)[m]!).map encR = d2Es Gs := by
  rw [List.map_map, d2Es, smapK_eq, rangeK_eq]
  apply List.map_congr_left
  intro m hmem
  have h := List.mem_range.1 hmem
  change encR ((eTab ws)[m]!) = d2E Gs m
  rw [hm m h, d2Es_get Gs h]

include hG in
theorem grp_of (hlen : ws.length = 4) (hk : d2GrpK Gs = true) : chkGrp ws = true := by
  have hE := fun {m} (h : m < 16) => eTab_enc ws Gs hG h
  unfold d2GrpK at hk
  simp only [andB_eq, Bool.and_eq_true] at hk
  obtain ⟨k1, k2, k3, k4⟩ := hk
  unfold chkGrp
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨hlen, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact List.all_eq_true.2 fun m hm => wf_bool (hE (List.mem_range.1 hm)).1
  · rw [eqRows_of (hE (by decide)) (id_enc hK)]
    exact k2
  · rw [allDistinct_enc _ (fun X hX => by
      obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hX
      exact (hE (List.mem_range.1 hm)).1), es_map ws Gs (fun m h => (hE h).2)]
    exact k1
  · refine List.all_eq_true.2 fun m hm => List.all_eq_true.2 fun m' hm' => ?_
    have h1 := List.mem_range.1 hm
    have h2 := List.mem_range.1 hm'
    rw [eqRows_of (mul_enc hK (hE h1) (hE h2)) (hE (xor_lt16 h1 h2))]
    exact allR_spec (allR_spec k3 m h1) m' h2
  · refine List.all_eq_true.2 fun k hkm => ?_
    have h1 := List.mem_range.1 hkm
    rw [eqRows_of (hG k h1) (hE (pow2_lt16 h1))]
    exact allR_spec k4 k h1

include hG in
theorem norm_of (hk : d2NormK Gs = true) : chkNorm ws = true := by
  have hE := fun {m} (h : m < 16) => eTab_enc ws Gs hG h
  unfold d2NormK at hk
  simp only [andB_eq, Bool.and_eq_true] at hk
  unfold chkNorm
  simp only [Bool.and_eq_true]
  refine ⟨List.all_eq_true.2 fun m hm => ?_, List.all_eq_true.2 fun m hm => ?_⟩
  · have h1 := List.mem_range.1 hm
    obtain ⟨m', hm', he⟩ := anyR_spec (allR_spec hk.1 m h1)
    refine List.any_eq_true.2 ⟨m', List.mem_range.2 hm', ?_⟩
    rw [eqRows_of (mul_enc hK xR_enc (hE h1)) (mul_enc hK (hE hm') xR_enc)]
    exact he
  · have h1 := List.mem_range.1 hm
    have h := allR_spec hk.2 m h1
    rw [eqRows_of (mul_enc hK xR_enc (hE (by omega : m + 1 < 16)))
      (mul_enc hK (hE (by omega : m + 1 < 16)) xR_enc), ← notB_eq]
    exact h

include hG in
theorem k0_of (hk : ∀ c < 105, d2K0K Gs c = true) : chkK0 ws = true := by
  obtain ⟨-, hmap, hwf⟩ := x0Orb_ok
  unfold chkK0
  simp only []
  refine List.all_eq_true.2 fun q hq => ?_
  have hq' := List.mem_range.1 hq
  have hM := mats_get hmap hwf hq'
  have hc : Nat.div q 64 < 105 := by change q / 64 < 105; omega
  have h := allR_spec (hk (Nat.div q 64) hc) (Nat.mod q 64) (by change q % 64 < 64; omega)
  have e : Nat.add (Nat.mul 64 (Nat.div q 64)) (Nat.mod q 64) = q := by
    change 64 * (q / 64) + q % 64 = q
    omega
  rw [e] at h
  unfold d2K0At at h
  have hall : ((List.range 4).map fun k => wR (ws.getD k [])).all
      (fun g => eqRows (mulRows (x0Orb.mats[q]!) g) (mulRows g (x0Orb.mats[q]!))) =
      allR 4 fun k => Nat.beq (mulJ c rm (CFSG.KD.X0O.MSF q) (getN one Gs k))
        (mulJ c rm (getN one Gs k) (CFSG.KD.X0O.MSF q)) := by
    rw [allR_eq, List.all_map]
    apply all_range_congr
    intro k hk4
    change eqRows _ _ = _
    rw [eqRows_of (mul_enc hK hM (hG k hk4)) (mul_enc hK (hG k hk4) hM)]
  have hord : ∀ r, ordRows (x0Orb.mats[q]!) r = !(d2NotOrd (CFSG.KD.X0O.MSF q) r) := by
    intro r
    unfold ordRows d2NotOrd
    rw [eqRows_of hM (id_enc hK), eqRows_of (pow_enc hK hM r) (id_enc hK), notB_eq, andB_eq, notB_eq,
      Bool.not_not]
  rw [hall, hord, hord, hord, Bool.not_not, Bool.not_not, Bool.not_not, ← notB_eq, ← andB_eq, ← andB_eq,
    ← orB_eq'']
  exact h

include hG in
theorem n_of {q i j : Nat} (hk : d2NK Gs q i j = true) : chkN ws = true := by
  obtain ⟨-, hmap, hwf⟩ := x0Orb_ok
  have hE := fun {m} (h : m < 16) => eTab_enc ws Gs hG h
  unfold d2NK at hk
  simp only [andB_eq, orB_eq'', Bool.and_eq_true, Bool.or_eq_true] at hk
  obtain ⟨k1, k2, k3, k4, k5⟩ := hk
  have hq := lt_of_blt k3
  have hi := lt_of_blt k4
  have hM := mats_get hmap hwf hq
  have hn := mul_enc hK hM (pow_enc hK (nRows_enc) (i + 1))
  unfold chkN chkNcore
  refine List.any_eq_true.2 ⟨q, List.mem_range.2 hq, List.any_eq_true.2 ⟨i, List.mem_range.2 hi, ?_⟩⟩
  simp only [Bool.and_eq_true]
  refine ⟨List.all_eq_true.2 fun e he => ?_, ?_⟩
  · unfold eList at he
    simp only [] at he
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 he
    have h1 := List.mem_range.1 hm
    obtain ⟨m', hm', hk'⟩ := anyR_spec (allR_spec k1 m h1)
    refine List.any_eq_true.2 ⟨(eTab ws)[m']!, ?_, ?_⟩
    · unfold eList
      exact List.mem_map.2 ⟨m', List.mem_range.2 hm', rfl⟩
    · rw [eqRows_of (mul_enc hK hn (hE h1)) (mul_enc hK (hE hm') hn)]
      exact hk'
  · have hj : j ∈ [2, 3, 4] := by
      rcases k2 with h | h | h
      · rw [Nat.eq_of_beq_eq_true h]
        simp
      · rw [Nat.eq_of_beq_eq_true h]
        simp
      · rw [Nat.eq_of_beq_eq_true h]
        simp
    refine List.any_eq_true.2 ⟨j, hj, ?_⟩
    rw [eqRows_of (mul_enc hK hn xR_enc) (mul_enc hK (pow_enc hK xR_enc j) hn)]
    exact k5

include hG in
theorem w_of {Q : Array V2} {Qn QIn : Nat} (hQ : WfA Q ∧ encR Q = Qn) (hk : d2WK Gs Qn QIn = true) :
    chkW ws Q = true := by
  have hE := fun {m} (h : m < 16) => eTab_enc ws Gs hG h
  unfold d2WK at hk
  simp only [andB_eq, Bool.and_eq_true] at hk
  obtain ⟨⟨k1, k2⟩, k3, k4⟩ := hk
  have hQI := invRows_enc hK hQ.1 k1 (by rw [hQ.2]; exact k2)
  have hc : ∀ m < 16, WfA (mulRows (mulRows ((eTab ws)[m]!) xR) ((eTab ws)[m]!)) ∧
      encR (mulRows (mulRows ((eTab ws)[m]!) xR) ((eTab ws)[m]!)) =
        mulJ c rm (mulJ c rm (getN one (d2Es Gs) m) d2X) (getN one (d2Es Gs) m) :=
    fun m h => mul_enc hK (mul_enc hK (hE h) xR_enc) (hE h)
  have hz := mul_enc hK (mul_enc hK hQ xR_enc) hQI
  unfold chkW
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨wf_bool hQ.1, wf_bool hQI.1⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [eqRows_of (mul_enc hK hQ hQI) (id_enc hK)]
    exact k2
  · refine List.all_eq_true.2 fun m hm => ?_
    have h1 := List.mem_range.1 hm
    rw [eqRows_of (mul_enc hK hQ (hE h1)) (mul_enc hK (hE h1) hQ)]
    exact allR_spec k3 m h1
  · have hwf : ∀ X ∈ ((List.range 16).map fun m => mulRows (mulRows ((eTab ws)[m]!) xR) ((eTab ws)[m]!)) ++
        [mulRows (mulRows Q xR) (invRows Q)], WfA X := by
      intro X hX
      rcases List.mem_append.1 hX with h | h
      · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
        exact (hc m (List.mem_range.1 hm)).1
      · rw [List.mem_singleton.1 h]
        exact hz.1
    rw [allDistinct_enc _ hwf, List.map_append, List.map_map, List.map_singleton, hz.2]
    have hm : List.map (encR ∘ fun m => mulRows (mulRows ((eTab ws)[m]!) xR) ((eTab ws)[m]!)) (List.range 16) =
        smapK (fun m => mulJ c rm (mulJ c rm (getN one (d2Es Gs) m) d2X) (getN one (d2Es Gs) m)) (rangeK 16) := by
      rw [smapK_eq, rangeK_eq]
      apply List.map_congr_left
      intro m hmem
      exact (hc m (List.mem_range.1 hmem)).2
    rw [hm]
    exact k4

include hG in
theorem chkAll_of {Q : Array V2} {Qn QIn : Nat} {q i j : Nat} (hlen : ws.length = 4)
    (hQ : WfA Q ∧ encR Q = Qn) (h1 : d2GrpK Gs = true) (h2 : d2NormK Gs = true)
    (h3 : ∀ c < 105, d2K0K Gs c = true) (h4 : d2NK Gs q i j = true) (h5 : d2WK Gs Qn QIn = true) :
    chkAll ws Q = true := by
  unfold chkAll
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨grp_of ws Gs hG hlen h1, norm_of ws Gs hG h2⟩, k0_of ws Gs hG h3⟩, n_of ws Gs hG h4⟩,
    w_of ws Gs hG hQ h5⟩

end CertificateChecks.KernelJ4Q

end
