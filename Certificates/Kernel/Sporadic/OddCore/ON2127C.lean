module

public import Certificates.Kernel.Sporadic.OddCore.ON2127CD
public meta import Certificates.Kernel.Sporadic.OddCore.ON2127CD
public meta import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.Kernel.LocalCompUnpack
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelSpor.ON2127C.C0 240 8 60
  CertificateChecks.KernelSpor.ON2127C.S0 CertificateChecks.KernelSpor.ON2127C.baseP 2
  CertificateChecks.KernelSpor.ON2127C.DP
#ks_rawchain CertificateChecks.KernelSpor.ON2127C.C1 240 8 60
  CertificateChecks.KernelSpor.ON2127C.S1 CertificateChecks.KernelSpor.ON2127C.baseP 2
  CertificateChecks.KernelSpor.ON2127C.DP
#ks_rawchain CertificateChecks.KernelSpor.ON2127C.C2 240 8 60
  CertificateChecks.KernelSpor.ON2127C.S2 CertificateChecks.KernelSpor.ON2127C.baseP 2
  CertificateChecks.KernelSpor.ON2127C.DP
#ks_rawchain CertificateChecks.KernelSpor.ON2127C.C3 240 8 60
  CertificateChecks.KernelSpor.ON2127C.S3 CertificateChecks.KernelSpor.ON2127C.baseP 2
  CertificateChecks.KernelSpor.ON2127C.DP
#ks_rawchain CertificateChecks.KernelSpor.ON2127C.C4 240 8 60
  CertificateChecks.KernelSpor.ON2127C.S4 CertificateChecks.KernelSpor.ON2127C.baseP 2
  CertificateChecks.KernelSpor.ON2127C.DP
#ks_rawchain CertificateChecks.KernelSpor.ON2127C.C5 240 8 60
  CertificateChecks.KernelSpor.ON2127C.S5 CertificateChecks.KernelSpor.ON2127C.baseP 2
  CertificateChecks.KernelSpor.ON2127C.DP
#ks_rawchain CertificateChecks.KernelSpor.ON2127C.C6 240 8 60
  CertificateChecks.KernelSpor.ON2127C.S6 CertificateChecks.KernelSpor.ON2127C.baseP 2
  CertificateChecks.KernelSpor.ON2127C.DP
#ks_rawchain CertificateChecks.KernelSpor.ON2127C.C7 240 8 60
  CertificateChecks.KernelSpor.ON2127C.S7 CertificateChecks.KernelSpor.ON2127C.baseP 2
  CertificateChecks.KernelSpor.ON2127C.DP
#ks_rawchain CertificateChecks.KernelSpor.ON2127C.C8 240 8 60
  CertificateChecks.KernelSpor.ON2127C.S8 CertificateChecks.KernelSpor.ON2127C.baseP 2
  CertificateChecks.KernelSpor.ON2127C.DP
#ks_rawchain CertificateChecks.KernelSpor.ON2127C.C9 240 8 60
  CertificateChecks.KernelSpor.ON2127C.S9 CertificateChecks.KernelSpor.ON2127C.baseP 2
  CertificateChecks.KernelSpor.ON2127C.DP
#ks_rawchain CertificateChecks.KernelSpor.ON2127C.C10 240 8 60
  CertificateChecks.KernelSpor.ON2127C.S10 CertificateChecks.KernelSpor.ON2127C.baseP 2
  CertificateChecks.KernelSpor.ON2127C.DP
#ks_rawchain CertificateChecks.KernelSpor.ON2127C.C11 240 8 60
  CertificateChecks.KernelSpor.ON2127C.S11 CertificateChecks.KernelSpor.ON2127C.baseP 2
  CertificateChecks.KernelSpor.ON2127C.DP

namespace CertificateChecks.KernelSpor.ON2127C

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.Native

@[expose] def PairChain (S : Array (Array Nat)) : Prop :=
  rawChainOK 240 (S.extract 0 2) S baseP (CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 6 DP) 1 =
    true ∧ (rawOrbitSizes 240 S baseP).prod = 40320

@[expose] noncomputable def pairSU (PS : Nat → Nat) : Array (Array Nat) :=
  Array.ofFn (n := 6) fun j => unpack 240 8 (PS j.val)

theorem pairSU_size (PS : Nat → Nat) : (pairSU PS).size = 6 := Array.size_ofFn

theorem pairSU_get (PS : Nat → Nat) {j : Nat} (hj : j < 6) :
    (pairSU PS)[j]! = unpack 240 8 (PS j) := by
  rw [pairSU, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem pair_chain {PS PSI LR TR TRI : Nat → Nat} {BP : Nat}
    (hB : allN 4 (fun t => Nat.beq baseP[t]! (pg 8 (mask 8) BP t)) = true)
    (hh : headK 240 8 (mask 8) (240 * 8) (pidn 240 8) PS PSI 6 2 DP 4 BP = true)
    (hl : LevelsOK 240 8 PS PSI LR TR TRI 6 4 BP)
    (hs : ∀ i < 4, ∀ s < 4, schK 240 8 (mask 8) (240 * 8) (pidn 240 8) PS PSI LR TR TRI 6 BP 4 i
      (stepsAt 240 8 PS 6 BP i) (s * 60) 60 = true)
    (hp : allN 6 (fun j => permOK 240 8 (mask 8) (240 * 8) (PS j) (PSI j)) = true)
    (hc : ((List.range 4).map fun i => rcnt (LR i)).prod = 40320) : PairChain (pairSU PS) := by
  have hb : Binds 240 8 PS 6 4 BP (pairSU PS) baseP :=
    ⟨by decide, by decide, by decide, pairSU_size PS, fun j hj => pairSU_get PS hj,
      rfl, fun t ht => Nat.eq_of_beq_eq_true (allN_spec hB t ht)⟩
  refine ⟨rawChainK_sound (NS := 4) (CH := 60) (chunks := 1) hb hh hl (by decide) hs, ?_⟩
  rw [rawOrbitSizesK_sound hb hp hl]
  exact hc

theorem chain0 : PairChain (pairSU C0.S) :=
  pair_chain (by quickRfl) C0.head C0.hl C0.hs (by quickRfl) (by decide +kernel)
theorem chain1 : PairChain (pairSU C1.S) :=
  pair_chain (by quickRfl) C1.head C1.hl C1.hs (by quickRfl) (by decide +kernel)
theorem chain2 : PairChain (pairSU C2.S) :=
  pair_chain (by quickRfl) C2.head C2.hl C2.hs (by quickRfl) (by decide +kernel)
theorem chain3 : PairChain (pairSU C3.S) :=
  pair_chain (by quickRfl) C3.head C3.hl C3.hs (by quickRfl) (by decide +kernel)
theorem chain4 : PairChain (pairSU C4.S) :=
  pair_chain (by quickRfl) C4.head C4.hl C4.hs (by quickRfl) (by decide +kernel)
theorem chain5 : PairChain (pairSU C5.S) :=
  pair_chain (by quickRfl) C5.head C5.hl C5.hs (by quickRfl) (by decide +kernel)
theorem chain6 : PairChain (pairSU C6.S) :=
  pair_chain (by quickRfl) C6.head C6.hl C6.hs (by quickRfl) (by decide +kernel)
theorem chain7 : PairChain (pairSU C7.S) :=
  pair_chain (by quickRfl) C7.head C7.hl C7.hs (by quickRfl) (by decide +kernel)
theorem chain8 : PairChain (pairSU C8.S) :=
  pair_chain (by quickRfl) C8.head C8.hl C8.hs (by quickRfl) (by decide +kernel)
theorem chain9 : PairChain (pairSU C9.S) :=
  pair_chain (by quickRfl) C9.head C9.hl C9.hs (by quickRfl) (by decide +kernel)
theorem chain10 : PairChain (pairSU C10.S) :=
  pair_chain (by quickRfl) C10.head C10.hl C10.hs (by quickRfl) (by decide +kernel)
theorem chain11 : PairChain (pairSU C11.S) :=
  pair_chain (by quickRfl) C11.head C11.hl C11.hs (by quickRfl) (by decide +kernel)

end CertificateChecks.KernelSpor.ON2127C

end
