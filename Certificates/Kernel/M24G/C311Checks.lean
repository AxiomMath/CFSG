module

public import Certificates.Data.Kernel.M24G.C311
public import Certificates.Data.Kernel.M24G.Lists
public import Certificates.Kernel.M24G.TrioData
public import Certificates.Kernel.M24G.TSData
public import Certificates.Kernel.M24G.DualData
public import Certificates.Kernel.M24G.C311Data

set_option maxRecDepth 100000

public section

namespace CFSG.KC.M24G.C311C

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

set_option maxHeartbeats 0 in
theorem lu_ts : allIdx (fun i x => x.contains 0 == DualD.LU.contains i) TS 0 = true := by
  decide +kernel

theorem ts_length : TS.length = 3795 := by decide +kernel

set_option maxHeartbeats 0 in
theorem ru_ok : DualD.LU.all (fun a => TS.toArray[a]! == tabRow DualD.LU C311D.RU a) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem ds_ok : discsOvalsT DualD.LU (tabLU DualD.LU DualD.TU) = C311D.DS := by
  decide +kernel

theorem ds_len : C311D.DS.length = 21 := by decide +kernel

set_option maxHeartbeats 0 in
theorem a_ok : (TL.zip TS).all (c311A C311D.DS (tabRow DualD.LU C311D.RU)
    (tabLU DualD.LU DualD.TU)) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem nb_ok : nbsOK TS DualD.LU C311D.NB C311D.MS = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem b_ok : c311B C311D.DS (fun d => (tabNM DualD.LU C311D.NB C311D.MS d).2) = true := by
  decide +kernel

end CFSG.KC.M24G.C311C
