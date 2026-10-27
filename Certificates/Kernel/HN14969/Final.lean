
module

public import Certificates.Kernel.HN14969.Checks
public import CFSG.Certificates.Kernel.HN14969.Theory
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Quasithin.Recognition.CertChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHN14969

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.HN14969 HNUnitaryBridge CFSG.Monster.B.Co2
  CFSG.Certificates.Native CFSG.RankThree.PartOne.HNB

@[expose] noncomputable def strongArr (kS n w : ℕ) (PS : ℕ → ℕ) : Array (Array ℕ) :=
  Array.ofFn (n := kS) fun j => unpack n w (PS j.val)

theorem strongArr_size (kS n w : ℕ) (PS : ℕ → ℕ) : (strongArr kS n w PS).size = kS := by
  simp [strongArr]

theorem strongArr_get {kS n w : ℕ} {PS : ℕ → ℕ} {j : ℕ} (hj : j < kS) :
    (strongArr kS n w PS)[j]! = unpack n w (PS j) := by
  rw [strongArr, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem binds_of {n w kS nb BP : ℕ} {PS : ℕ → ℕ} {base : List (Fin n)} (h0 : 0 < n)
    (h1 : n + 1 < 2 ^ w) (h2 : n < 65536) (hlen : base.length = nb)
    (hbase : ∀ t < nb, ((base.map Fin.val).toArray)[t]! = pg w (mask w) BP t) :
    Binds n w PS kS nb BP (strongArr kS n w PS) (base.map Fin.val).toArray :=
  ⟨h0, h1, h2, strongArr_size _ _ _ _, fun _ hj => strongArr_get hj, by simp [hlen], hbase⟩

theorem agreeL_spec {n : ℕ} {g h : ℕ → ℕ} (H : agreeL n g h = true) {i : ℕ} (hi : i < n) :
    g i = h i := by
  have := List.all_eq_true.1 H i (List.mem_range.2 hi)
  simpa using this

theorem card_pair {n w kS nb BP NS CH : ℕ} {PS PSI LR TR TRI : ℕ → ℕ} {D : List (List ℤ)}
    {base : List (Fin n)} (hn : 1 ≤ n) (hnd : base.Nodup) (hk : 2 ≤ kS)
    (hb : Binds n w PS kS nb BP (strongArr kS n w PS) (base.map Fin.val).toArray)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS 2 D nb BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP) (hNS : n ≤ NS * CH)
    (hs : ∀ i < nb, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i
      (stepsAt n w PS kS BP i) (s * CH) CH = true)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true) :
    Nat.card (Subgroup.closure ({permOfArr n (strongArr kS n w PS)[0]!,
      permOfArr n (strongArr kS n w PS)[1]!} : Set (Equiv.Perm (Fin n)))) =
      ((List.range nb).map fun i => rcnt (LR i)).prod := by
  have hraw := rawChainK_sound (chunks := 1) hb hh hl hNS hs
  have hsz : ((strongArr kS n w PS).extract 0 2).size = 2 := by
    simp [strongArr_size]
    omega
  have he : ∀ k < 2, ((strongArr kS n w PS).extract 0 2)[k]! = (strongArr kS n w PS)[k]! := by
    intro k hk
    rw [getElem!_pos _ k (by omega), getElem!_pos _ k (by rw [strongArr_size]; omega),
      Array.getElem_extract]
    simp
  have h := CFSG.Quasithin.card_closure_permOfArr_of_rawChainOK (n := n) hn
    (O := (strongArr kS n w PS).extract 0 2) (S := strongArr kS n w PS)
    (W := CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 kS D) hnd (chunks := 1) (by norm_num)
    (by rw [hsz, strongArr_size]; exact hk) (fun i hi => by rw [hsz] at hi; rw [he i hi])
    (by rw [hsz]; exact hraw)
  rw [rawOrbitSizesK_sound hb hp hl] at h
  have hset : ({permOfArr n (strongArr kS n w PS)[0]!, permOfArr n (strongArr kS n w PS)[1]!} :
      Set (Equiv.Perm (Fin n))) = {g | ∃ k < ((strongArr kS n w PS).extract 0 2).size,
        permOfArr n ((strongArr kS n w PS).extract 0 2)[k]! = g} := by
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
    rw [hsz]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, by norm_num, by rw [he 0 (by norm_num)]⟩
      · exact ⟨1, by norm_num, by rw [he 1 (by norm_num)]⟩
    · rintro ⟨k, hk, rfl⟩
      interval_cases k
      · exact Or.inl (by rw [he 0 (by norm_num)])
      · exact Or.inr (by rw [he 1 (by norm_num)])
  rw [hset]
  exact h

theorem bindsH : Binds 176 8 HC.S 7 4 HC.BP (strongArr 7 176 8 HC.S)
    (([50, 51, 52, 56] : List (Fin 176)).map Fin.val).toArray :=
  binds_of (by norm_num) (by norm_num) (by norm_num) rfl (by decide +kernel)

theorem bindsR : Binds 126 7 RC.S 7 4 RC.BP (strongArr 7 126 7 RC.S)
    (([0, 1, 2, 6] : List (Fin 126)).map Fin.val).toArray :=
  binds_of (by norm_num) (by norm_num) (by norm_num) rfl (by decide +kernel)

theorem bindsP : Binds 50 6 PC.S 9 4 PC.BP (strongArr 9 50 6 PC.S)
    (([0, 1, 2, 3] : List (Fin 50)).map Fin.val).toArray :=
  binds_of (by norm_num) (by norm_num) (by norm_num) rfl (by decide +kernel)

theorem cardH : Nat.card (Subgroup.closure ({permOfArr 176 (strongArr 7 176 8 HC.S)[0]!,
    permOfArr 176 (strongArr 7 176 8 HC.S)[1]!} : Set (Equiv.Perm (Fin 176)))) = 126000 := by
  rw [card_pair (NS := 11) (CH := 16) (by norm_num) (by decide) (by norm_num) bindsH HC.head HC.hl
    (by norm_num) HC.hs permH, sizesH]
  rfl

theorem cardR : Nat.card (Subgroup.closure ({permOfArr 126 (strongArr 7 126 7 RC.S)[0]!,
    permOfArr 126 (strongArr 7 126 7 RC.S)[1]!} : Set (Equiv.Perm (Fin 126)))) = 126000 := by
  rw [card_pair (NS := 8) (CH := 16) (by norm_num) (by decide) (by norm_num) bindsR RC.head RC.hl
    (by norm_num) RC.hs permR, sizesR]
  rfl

theorem cardP : Nat.card (Subgroup.closure ({permOfArr 50 (strongArr 9 50 6 PC.S)[0]!,
    permOfArr 50 (strongArr 9 50 6 PC.S)[1]!} : Set (Equiv.Perm (Fin 50)))) = 126000 := by
  rw [card_pair (NS := 5) (CH := 10) (by norm_num) (by decide) (by norm_num) bindsP PC.head PC.hl
    (by norm_num) PC.hs permP, sizesP]
  rfl

theorem sigmaAL_length : sigmaAL.length = 50 := by decide +kernel

theorem sigmaBL_length : sigmaBL.length = 50 := by decide +kernel

theorem nonempty_mulEquiv :
    Nonempty (Subgroup.closure (Set.range fun k : Fin 6 => permOfArr 50 smallPerms[(k : ℕ)]!) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSU 3 (5 ^ 1) CFSG.RankThree.PartOne.HNB.F25)) := by
  have pH0 := (CFSG.KS.Raw.Orb.prep_PS bindsH permH (j := 0) (by norm_num)).1
  have pH1 := (CFSG.KS.Raw.Orb.prep_PS bindsH permH (j := 1) (by norm_num)).1
  have pR0 := (CFSG.KS.Raw.Orb.prep_PS bindsR permR (j := 0) (by norm_num)).1
  have pR1 := (CFSG.KS.Raw.Orb.prep_PS bindsR permR (j := 1) (by norm_num)).1
  have pP0 := (CFSG.KS.Raw.Orb.prep_PS bindsP permP (j := 0) (by norm_num)).1
  have pP1 := (CFSG.KS.Raw.Orb.prep_PS bindsP permP (j := 1) (by norm_num)).1
  have eA : permOfArr 176 (strongArr 7 176 8 HC.S)[0]! =
      emb (permOfArr 50 (strongArr 9 50 6 PC.S)[0]!, permOfArr 126 (strongArr 7 126 7 RC.S)[0]!) := by
    refine eq_emb (fun x => ?_) (fun i => ?_)
    · exact (pH0 (Fin.castAdd 126 x)).symm.trans ((agreeL_spec splitP0 x.2).trans (pP0 x))
    · exact (pH0 (Fin.natAdd 50 i)).symm.trans ((agreeL_spec splitR0 i.2).trans
        (congrArg (50 + ·) (pR0 i)))
  have eB : permOfArr 176 (strongArr 7 176 8 HC.S)[1]! =
      emb (permOfArr 50 (strongArr 9 50 6 PC.S)[1]!, permOfArr 126 (strongArr 7 126 7 RC.S)[1]!) := by
    refine eq_emb (fun x => ?_) (fun i => ?_)
    · exact (pH1 (Fin.castAdd 126 x)).symm.trans ((agreeL_spec splitP1 x.2).trans (pP1 x))
    · exact (pH1 (Fin.natAdd 50 i)).symm.trans ((agreeL_spec splitR1 i.2).trans
        (congrArg (50 + ·) (pR1 i)))
  have mA : Moves iso (permOfArr 126 (strongArr 7 126 7 RC.S)[0]!) Umat := by
    rw [← decMat_lget_uCode]
    exact moves_of_actOK actU_ok fun i => (pR0 i).symm
  have mB : Moves iso (permOfArr 126 (strongArr 7 126 7 RC.S)[1]!) Vmat := by
    rw [← decMat_lget_vCode]
    exact moves_of_actOK actV_ok fun i => (pR1 i).symm
  rw [closure_smallPerms_eq words_ok (lrep_of_isListL genA sigmaAL_length pP0)
    (lrep_of_isListL genB sigmaBL_length pP1)]
  exact nonempty_mulEquiv_psu3_of_checks eA eB cardH cardP cardR iso_ok mA mB

end CertificateChecks.KernelHN14969

end
