module

public import CFSG.Certificates.Kernel.LocalQTSmallSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.GH74.Exceptional.LinearFourTwo
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Glue
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X35Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.Permutation.AlternatingAutomorphism.Conjugation
public import Certificates.Certificate113

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4032

open Equiv CFSG.KC.LQT.S

@[expose] def lb : List Nat :=
  [5573314592, 4402087968, 3360884768, 5574298656, 6581980192, 4469099552, 5572235296,
    6545379360, 3391295520, 4368471072, 6512841760, 3292730400, 2287048736, 2318538784,
    2252511264, 5574329408, 6582010944, 4469130304, 6613500992, 6547473472, 3393389632,
    5574264928, 6581946464, 4469065824, 6612357216, 6513792096, 2319489120, 5571184768,
    6544328832, 3390244992, 6611340416, 6510711936, 2316408960, 4334913696, 6479284384,
    3259173024, 6480268448, 6478205088, 2185336992, 1213302976, 1244793024, 1178765504,
    1245777088, 1243713728, 1145148608, 5574330369, 6582011905, 4469131265, 6613501953,
    6547474433, 3393390593, 6614486017, 6612422657, 6513857537, 2319554561, 5574328354,
    6582009890, 4469129250, 6613499938, 6547472418, 3393388578, 6614450274, 6611370114,
    6480298146, 1245806786, 5574232099, 6581913635, 4469032995, 6612324387, 6513759267,
    2319456291, 6614418499, 6611273859, 6480201891, 1245710531, 5570136100, 6543280164,
    3389196324, 6610291748, 6509663268, 2315360292, 6610322500, 6610258020, 6476105892,
    1241614532, 4301359141, 6445729829, 3225618469, 6446713893, 6444650533, 2151782437,
    6446744645, 6446680165, 6443600005, 1078036677, 139560998, 171051046, 105023526, 172035110,
    169971750, 71406630, 172065862, 172001382, 168921222, 37849254]

@[expose] def lc : List Nat :=
  [5574330400, 6582011936, 4469131296, 6613501984, 6547474464, 3393390624, 6614486048,
    6612422688, 6513857568, 2319554592, 6614516800, 6614452320, 6611372160, 6480300192,
    1245808832, 6614517761, 6614515746, 6614419491, 6610323492, 6446745637, 172066854]

@[expose] noncomputable def ts : List Nat :=
  [sw2 7 0 1 1 2, sw2 7 1 2 2 3, sw2 7 2 3 3 4, sw2 7 3 4 4 5, sw2 7 4 5 5 6]

theorem hts : [swap 0 1 * swap 1 2, swap 1 2 * swap 2 3, swap 2 3 * swap 3 4,
    swap 3 4 * swap 4 5, swap 4 5 * swap 5 6].map (code (n := 7)) = ts := by decide +kernel
theorem ta : c4032a [1, 3, 5] = true := by quickRfl
theorem td : c4032d 5 = true := by quickRfl
theorem te : c4032e ts = true := by quickRfl
theorem cb : invCover 3 lb = true := by quickRfl
theorem cc : invCover 5 lc = true := by quickRfl

@[expose] def lbAt (k : Nat) : Nat := lb.getD k 0

@[expose] def lcAt (k : Nat) : Nat := lc.getD k 0

@[expose] noncomputable def bF (k : Nat) : Bool := p22 (lbAt k)

@[expose] noncomputable def cF (k : Nat) : Bool := q2 (lcAt k)

#kc_each_unfold bF 0 105 as CFSG.KD.LQT.C4032.b eval lbAt
#kc_each_unfold cF 0 21 as CFSG.KD.LQT.C4032.c eval lcAt

#kc_forall_chunks b_all (fun k => p22 (lbAt k) = true) 105 CFSG.KD.LQT.C4032.b 1
#kc_forall_chunks c_all (fun k => q2 (lcAt k) = true) 21 CFSG.KD.LQT.C4032.c 1

theorem allb : ∀ s ∈ lb, p22 s = true := by
  intro s hs
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hs
  have h := b_all k (lt_of_lt_of_eq hk rfl)
  rwa [lbAt, List.getD_eq_getElem _ _ hk] at h

theorem allc : ∀ s ∈ lc, q2 s = true := by
  intro s hs
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hs
  have h := c_all k (lt_of_lt_of_eq hk rfl)
  rwa [lcAt, List.getD_eq_getElem _ _ hk] at h

end CFSG.KD.LQT.C4032

end
