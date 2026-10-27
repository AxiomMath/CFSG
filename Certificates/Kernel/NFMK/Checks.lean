module

public import Certificates.Kernel.NFMK.Data
public import Certificates.Kernel.WEMK.Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.NFMK

open Certificates.WEMK Certificates.HSMK Certificates.NFMK CFSG.KC.PCent

theorem n4_el : kEl 4 WEMK.N4.S N4.E (treeOf N4.E) N4.Yi N4.YW N4.ET N4.EN N4.Ep = true := by
  decide +kernel

theorem en4_el : kEl 4 WEMK.EN4.S EN4.E (treeOf EN4.E) EN4.Yi EN4.YW EN4.ET EN4.EN EN4.Ep = true := by
  decide +kernel

theorem n4_span : (kSpan 4 N4.E (treeOf N4.E) N4.B N4.CF && kWords 4 WEMK.N4.S N4.ZW N4.IW) = true := by
  decide +kernel

theorem en4_span : (kSpan 4 EN4.E (treeOf EN4.E) EN4.B EN4.CF && kWords 4 WEMK.EN4.S EN4.ZW EN4.IW) = true := by
  decide +kernel

theorem n4_cos : kCos 4 WEMK.N4.S N4.E N4.C (treeOf N4.C) (treeOf N4.E) N4.CT N4.CP = true := by
  decide +kernel

theorem en4_cos : kCos 4 WEMK.EN4.S EN4.E EN4.C (treeOf EN4.C) (treeOf EN4.E) EN4.CT EN4.CP = true := by
  decide +kernel

theorem n4_orb : kOrbT 4 WEMK.N4.S N4.E N4.C (treeOf N4.C) (treeOf N4.E) N4.OT (N4.W.map Prod.fst) = true := by
  decide +kernel

theorem en4_orb :
    kOrbT 4 WEMK.EN4.S EN4.E EN4.C (treeOf EN4.C) (treeOf EN4.E) EN4.OT (EN4.W.map Prod.fst) = true := by
  decide +kernel

theorem n4_scan : kScan 4 N4.E (treeOf N4.C) N4.C.length WEMK.N4.V N4.W = true := by
  decide +kernel

theorem en4_scan : kScan 4 EN4.E (treeOf EN4.C) EN4.C.length WEMK.EN4.V EN4.W = true := by
  decide +kernel

theorem n4_pair : kPairO 4 WEMK.N4.V = true := by
  decide +kernel

theorem en4_pair : kPairO 4 WEMK.EN4.V = true := by
  decide +kernel

theorem n4_chain : kChain 4 WEMK.N4.V N4.lv = true := by
  decide +kernel

theorem en4_chain : kChain 4 WEMK.EN4.V EN4.lv = true := by
  decide +kernel

theorem n4_lens : N4.lv.map (fun l => l.2.1.length) = [80, 12, 4, 2] := by
  decide +kernel

theorem en4_lens : EN4.lv.map (fun l => l.2.1.length) = [240, 12, 8, 2] := by
  decide +kernel

end CFSG.KD.NFMK

end
