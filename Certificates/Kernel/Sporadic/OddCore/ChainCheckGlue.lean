module

public import CFSG.Certificates.Kernel.Spor.StrongOfSound
public import CFSG.Sporadic.HNOddCore.ChainUtil
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem wordsArr_eq {kO kS : Nat} {D : List (List Int)} {W : Array (List Int)}
    (hs : W.size = kS) (hk : kO ≤ kS) (hW : ∀ j < kO, W[j]! = [])
    (hD : W.extract kO W.size = D.toArray) :
    W = CFSG.Sporadic.Schreier.Co3.Native.wordsArr kO kS D := by
  apply Array.ext
  · simp [CFSG.Sporadic.Schreier.Co3.Native.wordsArr, hs]
  · intro j h1 h2
    simp only [CFSG.Sporadic.Schreier.Co3.Native.wordsArr, Array.getElem_ofFn]
    split_ifs with h
    · rw [← getElem!_pos W j h1]
      exact hW j h
    · have e := congrArg (fun A : Array (List Int) => A[j - kO]?) hD
      simp only [Array.getElem?_extract] at e
      rw [List.getD_eq_getElem?_getD, ← List.getElem?_toArray, ← e]
      simp [show kO + (j - kO) = j by omega, h1, show j - kO < W.size - kO by omega]

theorem chainCheck_of {n w kS kO nb BP NS CH : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {O : Array (Array Nat)} {W : Array (List Int)} {D : List (List Int)} {base : List (Fin n)}
    {sizes : List Nat}
    (hO : O.size = kO ∧ ∀ j < kO, O[j]! = unpack n w (PS j))
    (hWs : W.size = kS) (hW0 : ∀ j < kO, W[j]! = []) (hD : W.extract kO W.size = D.toArray)
    (hn : 0 < n ∧ n + 1 < 2 ^ w ∧ n < 65536)
    (hbase : (base.map Fin.val).toArray.size = nb ∧
      ∀ t < nb, (base.map Fin.val).toArray[t]! = pg w (mask w) BP t)
    (hh : headK n w (mask w) (n * w) (pidn n w) PS PSI kS kO D nb BP = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hNS : n ≤ NS * CH)
    (hs : ∀ i < nb, ∀ s < NS, schK n w (mask w) (n * w) (pidn n w) PS PSI LR TR TRI kS BP nb i
      (stepsAt n w PS kS BP i) (s * CH) CH = true)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hsz : (List.range nb).map (fun i => rcnt (LR i)) = sizes) :
    CFSG.Sporadic.HNOddCore.chainCheck n O W base sizes = true := by
  have hk : kO ≤ kS := by
    unfold headK at hh
    exact Nat.le_of_ble_eq_true ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 ((bAnd_iff _ _).1 hh).2).2).1
  have hSe : CFSG.Sporadic.HNOddCore.strongArrs n O W =
      (CFSG.YGroups.ModelNative.strongOf n O D.toArray).1 := by
    unfold CFSG.Sporadic.HNOddCore.strongArrs
    rw [hO.1, hD]
  obtain ⟨hS1, hS2⟩ := strongOf_bind hO hh
  rw [← hSe] at hS1 hS2
  have hb : Binds n w PS kS nb BP (CFSG.Sporadic.HNOddCore.strongArrs n O W)
      (base.map Fin.val).toArray := ⟨hn.1, hn.2.1, hn.2.2, hS1, hS2, hbase.1, hbase.2⟩
  have hc := rawChainK_sound (chunks := 4) hb hh hl hNS hs
  rw [← wordsArr_eq hWs hk hW0 hD] at hc
  have hr := rawOrbitSizesK_sound hb hp hl
  unfold CFSG.Sporadic.HNOddCore.chainCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨by rw [hS1, hO.1]; exact hk, ?_⟩, by rw [← hO.1] at hc; exact hc⟩, by rw [hr, hsz]⟩
  rw [CFSG.ONSchreier.allBelowN_iff]
  intro i hi
  rw [hO.1] at hi
  rw [hS2 i (by omega), hO.2 i hi]
  exact beq_self_eq_true _

end CFSG.KS.Raw

end
