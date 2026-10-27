module

public import Certificates.Kernel.Sporadic.OddCore.ChainCheckGlue
public import Certificates.Kernel.Sporadic.OddCore.SuzC1BF
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Sporadic.SuzRecog.ModelGroupsChecks
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.SuzMGCG

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2.Native

theorem chainOK_of {kS kO nb BP NS CH : Nat} {PS PSI LR TR TRI : Nat → Nat}
    {S : Array (Array Nat)} {W : Array (List Int)} {D : List (List Int)} {base : List Nat}
    {orbits : List Nat}
    (hb : Binds 1782 11 PS kS nb BP S base.toArray)
    (hWs : W.size = kS) (hW0 : ∀ j < kO, W[j]! = []) (hD : W.extract kO W.size = D.toArray)
    (hh : headK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) PS PSI kS kO D nb BP = true)
    (hl : LevelsOK 1782 11 PS PSI LR TR TRI kS nb BP)
    (hNS : 1782 ≤ NS * CH)
    (hs : ∀ i < nb, ∀ s < NS, schK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) PS PSI LR TR TRI
      kS BP nb i (stepsAt 1782 11 PS kS BP i) (s * CH) CH = true)
    (hp : allN kS (fun j => permOK 1782 11 (mask 11) (1782 * 11) (PS j) (PSI j)) = true)
    (hsz : (List.range nb).map (fun i => rcnt (LR i)) = orbits) (hk : kO ≤ kS) :
    CFSG.Sporadic.SuzRecog.ModelGroupsCheck.chainOK S kO base W orbits = true := by
  have hc := rawChainK_sound (chunks := 4) hb hh hl hNS hs
  rw [← wordsArr_eq hWs hk hW0 hD] at hc
  unfold CFSG.Sporadic.SuzRecog.ModelGroupsCheck.chainOK
  rw [hc, rawOrbitSizesK_sound hb hp hl, hsz]
  simp

theorem strong_bind {cs : List Char} {s : String} {F : Nat → Nat} {N : Nat}
    (hs : s = String.ofList cs) (h : CFSG.KC.Misc.HexFlat.hexFlat cs 3 1782 11 N F = true)
    {PS : Nat → Nat} (hP : allN N (fun j => Nat.beq (PS j) (F j)) = true) :
    ∀ j < N, (Array.ofFn fun i : Fin N => hexTable 3 1782 (1782 * i.val) s)[j]! =
      unpack 1782 11 (PS j) := by
  intro j hj
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn,
    Nat.eq_of_beq_eq_true (allN_spec hP j hj)]
  exact CertificateChecks.KernelSpor.SuzMGF.hexJ_eq hs h hj

end CertificateChecks.KernelSpor.SuzMGCG

end
