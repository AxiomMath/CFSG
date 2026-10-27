module

public import Certificates.Kernel.Sporadic.Fi22.M2079
public import Certificates.Kernel.Sporadic.Fi22.C2066
public import Certificates.Kernel.Sporadic.Fi22.C3147
public import CFSG.Certificates.Kernel.Spor.StrongOfFold
public import CFSG.Certificates.Kernel.Spor.BaseExt
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylow
import CFSG.Certificates.Kernel.Spor.GraphSepProof
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fo22C

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.ConjTree
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CertificateChecks.KernelSpor

theorem binds_ofFn {n w kS nb BP : Nat} {PS PS' : Nat → Nat} {base : Array Nat}
    (h0 : 0 < n) (h1 : n + 1 < 2 ^ w) (h2 : n < 65536) (hbs : base.size = nb)
    (hbp : allN nb (fun t => Nat.beq base[t]! (pg w (mask w) BP t)) = true)
    (hPS : allN kS (fun j => Nat.beq (PS' j) (PS j)) = true) :
    Binds n w PS' kS nb BP (Array.ofFn (n := kS) fun j => unpack n w (PS j.val)) base := by
  refine ⟨h0, h1, h2, by simp, fun j hj => ?_, hbs,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec hbp t ht)⟩
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn,
    Nat.eq_of_beq_eq_true (allN_spec hPS j hj)]

theorem ofFn_get {n w kS : Nat} {PS : Nat → Nat} {j : Nat} (hj : j < kS) :
    (Array.ofFn (n := kS) fun j => unpack n w (PS j.val))[j]! = unpack n w (PS j) := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem rep_of_perm {n w p q : Nat} (h : permOK n w (mask w) (n * w) p q = true) :
    Rep n (unpack n w p) (permOfArr n (unpack n w p)) ∧
      isInvA n (unpack n w p) (invCand n (unpack n w p)) = true := by
  have h' := invEqK_sound h
  rw [h'.1]
  exact ⟨(rep_permOfArr h'.2).1, h'.2⟩

theorem mem_P {p q : Nat}
    (hc : Fi22X.cn p = true) (hs : Fi22X.siftP p = true)
    (hp : permOK 3510 12 (mask 12) (3510 * 12) p q = true) :
    permOfArr 3510 (unpack 3510 12 p) ∈ fi22P :=
  (fi22InP_iff (rep_of_perm hp).1).1
    (Fi22C2066.fi22InP_of (PS := fun _ => p) (j := 0) (g := unpack 3510 12 p) rfl hc hs)

noncomputable abbrev SA (n w kS : Nat) (PS : Nat → Nat) : Array (Array Nat) :=
  Array.ofFn (n := kS) fun j => unpack n w (PS j.val)

noncomputable abbrev SN3 : Array (Array Nat) := SA 3510 12 7 Fo22N3.S
noncomputable abbrev SN4 : Array (Array Nat) := SA 3510 12 7 Fo22N4.S
noncomputable abbrev SP3 : Array (Array Nat) := SA 1575 11 11 Fo22P3.S
noncomputable abbrev SP4 : Array (Array Nat) := SA 63 7 11 Fo22P4.S
noncomputable abbrev SP2 : Array (Array Nat) := SA 27 5 11 Fo22P2.S

theorem rN3 : allN 7 (fun j => Nat.beq (Fo22N3.S j) (Fo22N3.S j)) = true := by quickRfl
theorem rN4 : allN 7 (fun j => Nat.beq (Fo22N4.S j) (Fo22N4.S j)) = true := by quickRfl
theorem rP3 : allN 11 (fun j => Nat.beq (Fo22P3.S j) (Fo22P3.S j)) = true := by quickRfl
theorem rP4 : allN 11 (fun j => Nat.beq (Fo22P4.S j) (Fo22P4.S j)) = true := by quickRfl
theorem rP2 : allN 11 (fun j => Nat.beq (Fo22P2.S j) (Fo22P2.S j)) = true := by quickRfl

theorem bindsN3 : Binds 3510 12 Fo22N3.S 7 4 Fo22N3.BP SN3 #[9, 0, 1, 2] :=
  binds_ofFn (by norm_num) (by norm_num) (by norm_num) rfl Fo22M.bN3 rN3
theorem bindsN3x : Binds 3510 12 Fo22N3x.S 7 7 Fo22N3x.BP SN3 #[9, 0, 1, 2, 3, 6, 4] :=
  binds_ofFn (by norm_num) (by norm_num) (by norm_num) rfl Fo22M.bN3x Fo22M.sN3
theorem bindsN4 : Binds 3510 12 Fo22N4.S 7 3 Fo22N4.BP SN4 #[0, 1, 2] :=
  binds_ofFn (by norm_num) (by norm_num) (by norm_num) rfl Fo22M.bN4 rN4
theorem bindsN4x : Binds 3510 12 Fo22N4x.S 7 6 Fo22N4x.BP SN4 #[0, 1, 2, 3, 6, 4] :=
  binds_ofFn (by norm_num) (by norm_num) (by norm_num) rfl Fo22M.bN4x Fo22M.sN4
theorem bindsP3 : Binds 1575 11 Fo22P3.S 11 5 Fo22P3.BP SP3 #[0, 1, 2, 4, 3] :=
  binds_ofFn (by norm_num) (by norm_num) (by norm_num) rfl Fo22M.bP3 rP3
theorem bindsGP3 : Binds 1575 11 Fo22GP3.PS 11 5 Fo22GP3.BP SP3 #[0, 1, 2, 4, 3] :=
  binds_ofFn (by norm_num) (by norm_num) (by norm_num) rfl Fo22M.bGP3 Fo22M.sP3
theorem bindsP4 : Binds 63 7 Fo22P4.S 11 6 Fo22P4.BP SP4 #[0, 1, 2, 4, 3, 5] :=
  binds_ofFn (by norm_num) (by norm_num) (by norm_num) rfl Fo22M.bP4 rP4
theorem bindsP2 : Binds 27 5 Fo22P2.S 11 6 Fo22P2.BP SP2 #[0, 1, 2, 3, 5, 7] :=
  binds_ofFn (by norm_num) (by norm_num) (by norm_num) rfl Fo22M.bP2 rP2

theorem two_get {α : Type} [Inhabited α] {a b : α} {k : Nat} (hk : k < 2) :
    (#[a, b] : Array α)[k]! = if k = 0 then a else b := by
  interval_cases k <;> rfl

theorem orig2 {n w kS : Nat} {PS : Nat → Nat} {a b : Array Nat} (hk : 2 ≤ kS)
    (ha : a = unpack n w (PS 0)) (hb : b = unpack n w (PS 1)) :
    (#[a, b] : Array (Array Nat)).size = 2 ∧
      ∀ k < 2, (#[a, b] : Array (Array Nat))[k]! = (SA n w kS PS)[k]! := by
  refine ⟨rfl, fun k hk' => ?_⟩
  rw [ofFn_get (by omega)]
  interval_cases k
  · exact ha
  · exact hb

theorem bind_of {F P : Nat} {n w : Nat} {a : Array Nat} (ha : a = unpack n w F)
    (h : Nat.beq F P = true) : a = unpack n w P := by
  rw [ha, Nat.eq_of_beq_eq_true h]

theorem n3S : fo22N3Strong = SN3 := by
  obtain ⟨h0, h1⟩ := (bAnd_iff (Nat.beq Fo22T.A3.F (Fo22N3.S 0))
    (Nat.beq Fo22T.B3.F (Fo22N3.S 1))).1 Fo22M.oN3
  obtain ⟨hs, hg⟩ := orig2 (n := 3510) (w := 12) (kS := 7) (PS := Fo22N3.S) (by norm_num)
    (bind_of Fo22T.a3_eq h0) (bind_of Fo22T.b3_eq h1)
  rw [fo22N3Strong]
  exact strongOf_eq bindsN3 Fo22N3.head (by norm_num) hs hg Fo22W.n3W

theorem n4S : fo22N4Strong = SN4 := by
  obtain ⟨h0, h1⟩ := (bAnd_iff (Nat.beq Fo22T.A4.F (Fo22N4.S 0))
    (Nat.beq Fo22T.B4.F (Fo22N4.S 1))).1 Fo22M.oN4
  obtain ⟨hs, hg⟩ := orig2 (n := 3510) (w := 12) (kS := 7) (PS := Fo22N4.S) (by norm_num)
    (bind_of Fo22T.a4_eq h0) (bind_of Fo22T.b4_eq h1)
  rw [fo22N4Strong]
  exact strongOf_eq bindsN4 Fo22N4.head (by norm_num) hs hg Fo22W.n4W

theorem p3S : fo22P3Strong = SP3 := by
  obtain ⟨h0, h1⟩ := (bAnd_iff (Nat.beq Fo22T.Pa3.F (Fo22P3.S 0))
    (Nat.beq Fo22T.Pb3.F (Fo22P3.S 1))).1 Fo22M.oP3
  obtain ⟨hs, hg⟩ := orig2 (n := 1575) (w := 11) (kS := 11) (PS := Fo22P3.S) (by norm_num)
    (bind_of Fo22T.pa3_eq h0) (bind_of Fo22T.pb3_eq h1)
  rw [fo22P3Strong]
  exact strongOf_eq bindsP3 Fo22P3.head (by norm_num) hs hg Fo22W.p3W

theorem p4S : fo22P4Strong = SP4 := by
  obtain ⟨h0, h1⟩ := (bAnd_iff (Nat.beq Fo22T.Pa4.F (Fo22P4.S 0))
    (Nat.beq Fo22T.Pb4.F (Fo22P4.S 1))).1 Fo22M.oP4
  obtain ⟨hs, hg⟩ := orig2 (n := 63) (w := 7) (kS := 11) (PS := Fo22P4.S) (by norm_num)
    (bind_of Fo22T.pa4_eq h0) (bind_of Fo22T.pb4_eq h1)
  rw [fo22P4Strong]
  exact strongOf_eq bindsP4 Fo22P4.head (by norm_num) hs hg Fo22W.p4W

theorem rows2 : ∀ k < 3, (rowsOf 27 fo22P2Flat)[k]! = unpack 27 5 (Fo22P2.S k) := by
  rw [Fo22T.p2_eq]
  decide +kernel

theorem p2S : fo22P2Strong = SP2 := by
  rw [fo22P2Strong]
  refine strongOf_eq bindsP2 Fo22P2.head (by norm_num) ?_ (fun k hk => ?_) Fo22W.p2W
  · rw [Fo22T.p2_eq]
    decide +kernel
  · have hk3 : k < 3 := hk
    rw [rows2 k hk3, ofFn_get (by omega)]

theorem sepP7
    {G : Equiv.Perm (Fin 3510)} (hG : G ∈ fi22P)
    (hfix : ∀ t < (#[9, 0, 1, 2, 3, 6, 4] : Array Nat).size,
      ∀ h : (#[9, 0, 1, 2, 3, 6, 4] : Array Nat)[t]! < 3510,
        G ⟨(#[9, 0, 1, 2, 3, 6, 4] : Array Nat)[t]!, h⟩ =
          ⟨(#[9, 0, 1, 2, 3, 6, 4] : Array Nat)[t]!, h⟩) : G = 1 := by
  refine Fi22C2066.fi22P_sep hG fun t ht h => ?_
  have ht6 : t < 6 := ht
  interval_cases t
  · exact Fi22C3147.fix_of_base hfix 1 (by decide) _ rfl h
  · exact Fi22C3147.fix_of_base hfix 2 (by decide) _ rfl h
  · exact Fi22C3147.fix_of_base hfix 3 (by decide) _ rfl h
  · exact Fi22C3147.fix_of_base hfix 4 (by decide) _ rfl h
  · exact Fi22C3147.fix_of_base hfix 5 (by decide) _ rfl h
  · exact Fi22C3147.fix_of_base hfix 6 (by decide) _ rfl h

theorem closure_le_P {kS : Nat}
    {PS PSI : Nat → Nat} (hc : allN kS (fun j => bAnd(Fi22X.cn (PS j), bAnd(Fi22X.cn (PSI j),
      permOK 3510 12 (mask 12) (3510 * 12) (PS j) (PSI j)))) = true)
    (hs : allN kS (fun j => Fi22X.siftP (PS j)) = true) :
    Subgroup.closure {g : Equiv.Perm (Fin 3510) |
      ∃ j < (SA 3510 12 kS PS).size, permOfArr 3510 (SA 3510 12 kS PS)[j]! = g} ≤ fi22P := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨j, hj, rfl⟩
  have hj' : j < kS := by simpa using hj
  obtain ⟨h1, -, h3⟩ := by simpa only [bAnd_iff] using allN_spec hc j hj'
  rw [ofFn_get hj']
  exact mem_P h1 (allN_spec hs j hj') h3

theorem sepN3x :
    Sep 3510 SN3 #[9, 0, 1, 2, 3, 6, 4] := fun _ hG hfix =>
  sepP7 (closure_le_P Fo22M.cnN3 Fo22M.pN3 hG) hfix

theorem sepN4x :
    Sep 3510 SN4 #[0, 1, 2, 3, 6, 4] := fun _ hG hfix =>
  Fi22C2066.fi22P_sep (closure_le_P Fo22M.cnN4 Fo22M.pN4 hG) hfix

@[expose] def finL (l : List Nat) : List (Fin 3510) := l.map fun x => ⟨x % 3510, Nat.mod_lt _ (by decide)⟩

theorem chainN3x :
    rawChainOK 3510 (SN3.extract 0 2) SN3 #[9, 0, 1, 2, 3, 6, 4]
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 7 Fo22W.n3D) 4 = true :=
  rawChainTK_sound bindsN3x Fo22N3x.head Fo22N3x.tl Fo22N3x.hst sepN3x Fo22N3x.hs (by norm_num)

theorem chainN4x :
    rawChainOK 3510 (SN4.extract 0 2) SN4 #[0, 1, 2, 3, 6, 4]
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 7 Fo22W.n4D) 4 = true :=
  rawChainTK_sound bindsN4x Fo22N4x.head Fo22N4x.tl Fo22N4x.hst sepN4x Fo22N4x.hs (by norm_num)

theorem sepN3 :
    Sep 3510 SN3 #[9, 0, 1, 2] := by
  refine sep_of_ext (by norm_num) (k := 2) (by simp) (by norm_num) (base := finL [9, 0, 1, 2])
    (ext := finL [9, 0, 1, 2, 3, 6, 4]) (baseArr := #[9, 0, 1, 2])
    (extArr := #[9, 0, 1, 2, 3, 6, 4]) (by decide) rfl rfl (by decide) chainN3x
    (fun i hi1 hi2 => ?_) sepN3x
  have hi : i < 7 := by simpa [finL] using hi2
  have hi4 : 4 ≤ i := by simpa [finL] using hi1
  rw [rawLevels_get (by simpa using hi),
    (levelTK_sound bindsN3x Fo22N3x.head Fo22N3x.tl hi).2]
  have h := allN_spec Fo22M.last3 (i - 4) (by omega)
  have e4 : Nat.add 4 (i - 4) = i := by
    rw [Nat.add_eq]
    omega
  rw [e4] at h
  exact Nat.eq_of_beq_eq_true h

theorem sepN4 :
    Sep 3510 SN4 #[0, 1, 2] := by
  refine sep_of_ext (by norm_num) (k := 2) (by simp) (by norm_num) (base := finL [0, 1, 2])
    (ext := finL [0, 1, 2, 3, 6, 4]) (baseArr := #[0, 1, 2])
    (extArr := #[0, 1, 2, 3, 6, 4]) (by decide) rfl rfl (by decide) chainN4x
    (fun i hi1 hi2 => ?_) sepN4x
  have hi : i < 6 := by simpa [finL] using hi2
  have hi3 : 3 ≤ i := by simpa [finL] using hi1
  rw [rawLevels_get (by simpa using hi),
    (levelTK_sound bindsN4x Fo22N4x.head Fo22N4x.tl hi).2]
  have h := allN_spec Fo22M.last4 (i - 3) (by omega)
  have e3 : Nat.add 3 (i - 3) = i := by
    rw [Nat.add_eq]
    omega
  rw [e3] at h
  exact Nat.eq_of_beq_eq_true h

theorem sepP3 : Sep 1575 SP3 #[0, 1, 2, 4, 3] :=
  CFSG.KS.GraphSep.graphSep_sound bindsGP3
    (CFSG.KS.GraphSep.list_of_sl (NS := 25) (CH := 64) (by norm_num) Fo22GP3.hL)
    (CFSG.KS.GraphSep.inv_of_sl (NS := 25) (CH := 64) (by norm_num) Fo22GP3.hI) Fo22GP3.ord
    (CFSG.KS.GraphSep.ref_of_sl (NS := 25) (CH := 64) (by norm_num) Fo22GP3.hR)

theorem chainN3 :
    rawChainOK 3510 (SN3.extract 0 2) SN3 #[9, 0, 1, 2]
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 7 Fo22W.n3D) 4 = true :=
  rawChainTK_sound bindsN3 Fo22N3.head Fo22N3.tl Fo22N3.hst sepN3 Fo22N3.hs (by norm_num)

theorem chainN4 :
    rawChainOK 3510 (SN4.extract 0 2) SN4 #[0, 1, 2]
      (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 7 Fo22W.n4D) 4 = true :=
  rawChainTK_sound bindsN4 Fo22N4.head Fo22N4.tl Fo22N4.hst sepN4 Fo22N4.hs (by norm_num)

theorem chainP3 : rawChainOK 1575 (SP3.extract 0 2) SP3 #[0, 1, 2, 4, 3]
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 11 Fo22W.p3D) 4 = true :=
  rawChainTK_sound bindsP3 Fo22P3.head Fo22P3.tl Fo22P3.hst sepP3 Fo22P3.hs (by norm_num)

theorem chainP4 : rawChainOK 63 (SP4.extract 0 2) SP4 #[0, 1, 2, 4, 3, 5]
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 11 Fo22W.p4D) 4 = true :=
  rawChainK_sound (NS := 8) (CH := 8) bindsP4 Fo22P4.head Fo22P4.hl (by norm_num) Fo22P4.hs

theorem chainP2 : rawChainOK 27 (SP2.extract 0 3) SP2 #[0, 1, 2, 3, 5, 7]
    (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 11 Fo22W.p2D) 4 = true :=
  rawChainK_sound (NS := 4) (CH := 8) bindsP2 Fo22P2.head Fo22P2.hl (by norm_num) Fo22P2.hs

theorem permP4 : allN 11 (fun j => permOK 63 7 (mask 7) (63 * 7) (Fo22P4.S j) (Fo22P4.SI j)) =
    true := by quickRfl
theorem permP2 : allN 11 (fun j => permOK 27 5 (mask 5) (27 * 5) (Fo22P2.S j) (Fo22P2.SI j)) =
    true := by quickRfl

theorem prodN3 : ((List.range 4).map fun i => rcnt (Fo22N3.LR i)).prod = 174182400 := by
  decide +kernel
theorem prodN4 : ((List.range 3).map fun i => rcnt (Fo22N4.LR i)).prod = 1451520 := by
  decide +kernel
theorem prodP3 : ((List.range 5).map fun i => rcnt (Fo22P3.LR i)).prod = 174182400 := by
  decide +kernel
theorem prodP4 : ((List.range 6).map fun i => rcnt (Fo22P4.LR i)).prod = 1451520 := by
  decide +kernel
theorem prodP2 : ((List.range 6).map fun i => rcnt (Fo22P2.LR i)).prod = 51840 := by
  decide +kernel

theorem chainOK_of {n kS ord nb k : Nat} {S : Array (Array Nat)} {base : Array Nat}
    {W : Array (List Int)} {LR : Nat → Nat} (hsz : S.size = kS)
    (hc : rawChainOK n (S.extract 0 k) S base W 4 = true)
    (ho : rawOrbitSizes n S base = (List.range nb).map fun i => rcnt (LR i))
    (hp : ((List.range nb).map fun i => rcnt (LR i)).prod = ord) :
    fo22ChainOK n S base W k kS ord = true := by
  unfold fo22ChainOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨hsz, hc⟩, by rw [ho, hp]⟩

theorem chains :
    fo22ChainOK 3510 fo22N3Strong #[9, 0, 1, 2] fo22N3Words 2 7 174182400 = true ∧
    fo22ChainOK 1575 fo22P3Strong #[0, 1, 2, 4, 3] fo22P3Words 2 11 174182400 = true ∧
    fo22ChainOK 3510 fo22N4Strong #[0, 1, 2] fo22N4Words 2 7 1451520 = true ∧
    fo22ChainOK 63 fo22P4Strong #[0, 1, 2, 4, 3, 5] fo22P4Words 2 11 1451520 = true ∧
    fo22ChainOK 27 fo22P2Strong #[0, 1, 2, 3, 5, 7] fo22P2Words 3 11 51840 = true := by
  rw [n3S, p3S, n4S, p4S, p2S, Fo22W.n3W, Fo22W.p3W, Fo22W.n4W, Fo22W.p4W, Fo22W.p2W]
  exact ⟨chainOK_of (by simp) chainN3 (rawOrbitSizesTK_sound bindsN3 Fo22N3.head Fo22N3.tl) prodN3,
    chainOK_of (by simp) chainP3 (rawOrbitSizesTK_sound bindsP3 Fo22P3.head Fo22P3.tl) prodP3,
    chainOK_of (by simp) chainN4 (rawOrbitSizesTK_sound bindsN4 Fo22N4.head Fo22N4.tl) prodN4,
    chainOK_of (by simp) chainP4 (rawOrbitSizesK_sound bindsP4 permP4 Fo22P4.hl) prodP4,
    chainOK_of (by simp) chainP2 (rawOrbitSizesK_sound bindsP2 permP2 Fo22P2.hl) prodP2⟩

end CertificateChecks.KernelSpor.Fo22C

end
