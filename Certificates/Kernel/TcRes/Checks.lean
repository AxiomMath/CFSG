module

public import Certificates.Kernel.TcRes.RootE6
public import Certificates.Kernel.TcRes.RootE8
public import Certificates.Kernel.TcRes.ForestA
public import Certificates.Kernel.TcRes.ForestB
public import Certificates.Kernel.TcRes.PlaneA
public import Certificates.Kernel.TcRes.PlaneB
public import Certificates.Kernel.TcRes.MovedA
public import Certificates.Kernel.TcRes.TransA
public import Certificates.Kernel.TcRes.C2PlaneA
public import Certificates.Kernel.TcRes.C2MovedA
public import Certificates.Kernel.TcRes.C3A
import CFSG.Certificates.Kernel.Common.ForallTreeFrom

public section

namespace CFSG.KD.TcRes.ch715750all

#kc_forall_tree e6_root (fun i => CFSG.KD.TcRes.E6.root i = true) 72
  CFSG.KD.TcRes.ch715750e6.root
#kc_forall_tree e6_row (fun g => CFSG.KD.TcRes.E6.row g = true) 72 CFSG.KD.TcRes.ch715750e6.row
#kc_forall_tree e8_root (fun i => CFSG.KD.TcRes.E8.root i = true) 240
  CFSG.KD.TcRes.ch715750e8.root
#kc_forall_tree e8_row (fun g => CFSG.KD.TcRes.E8.row g = true) 240
  CFSG.KD.TcRes.ch715750e8.row

#kc_forall_tree c1_rep (fun k => CFSG.KD.TcRes.C1.rep k = true) 25 CFSG.KD.TcRes.ch715750c1.rep
#kc_forall_tree c1_leaf (fun L => CFSG.KD.TcRes.C1.leaf L = true) 810
  CFSG.KD.TcRes.ch715750c1.leaf

#kc_forall_tree p_tab (fun i => CFSG.KD.TcRes.C1P.tab i = true) 9 CFSG.KD.TcRes.ch715750p.tab
#kc_forall_tree p_rc (fun g => CFSG.KD.TcRes.C1P.rc g = true) 72 CFSG.KD.TcRes.ch715750p.rc
#kc_forall_tree p_pw (fun k => CFSG.KD.TcRes.C1P.pw k = true) 25 CFSG.KD.TcRes.ch715750p.pw
#kc_forall_tree p_swLo (fun q => CFSG.KD.TcRes.C1P.sw q = true) 70 CFSG.KD.TcRes.ch715750p.sw
#kc_forall_tree_from p_swHi (fun q => CFSG.KD.TcRes.C1P.sw q = true) 72 3
  CFSG.KD.TcRes.ch715750p.sw
#kc_forall_tree p_leaf (fun L => CFSG.KD.TcRes.C1P.leaf L = true) 117
  CFSG.KD.TcRes.ch715750p.leaf

theorem p_sw : ∀ q < 75, q ≠ 70 → q ≠ 71 → CFSG.KD.TcRes.C1P.sw q = true := by
  have hlo : ∀ q < 70, CFSG.KD.TcRes.C1P.sw q = true := p_swLo
  have hhi : ∀ k < 3, CFSG.KD.TcRes.C1P.sw (72 + k) = true := p_swHi
  intro q hq h70 h71
  by_cases h : q < 70
  · exact hlo q h
  · have := hhi (q - 72) (by omega)
    rwa [Nat.add_sub_cancel' (by omega)] at this

#kc_forall_tree m_pos (fun g => CFSG.KD.TcRes.C1M.pos g = true) 72 CFSG.KD.TcRes.ch715750m.pos
#kc_forall_tree m_dec (fun g => CFSG.KD.TcRes.C1M.dec g = true) 72 CFSG.KD.TcRes.ch715750m.dec
#kc_forall_tree m_line (fun i => CFSG.KD.TcRes.C1M.line i = true) 234
  CFSG.KD.TcRes.ch715750m.line
#kc_forall_tree m_leaf (fun L => CFSG.KD.TcRes.C1M.leaf L = true) 117
  CFSG.KD.TcRes.ch715750m.mleaf

#kc_forall_tree t_q (fun g => CFSG.KD.TcRes.E8T.q g = true) 240 CFSG.KD.TcRes.ch715751t.q
#kc_forall_tree t_mv (fun g => CFSG.KD.TcRes.E8T.mv g = true) 240 CFSG.KD.TcRes.ch715751t.mv
#kc_forall_tree t_nd (fun i => CFSG.KD.TcRes.E8T.nd i = true) 550 CFSG.KD.TcRes.ch715751t.nd

#kc_forall_tree c2p_tab (fun i => CFSG.KD.TcRes.C2P.tab i = true) 5 CFSG.KD.TcRes.ch715751p.tab
#kc_forall_tree c2p_rc (fun g => CFSG.KD.TcRes.C2P.rc g = true) 240 CFSG.KD.TcRes.ch715751p.rc
#kc_forall_tree c2p_sw (fun q => CFSG.KD.TcRes.C2P.sw q = true) 2 CFSG.KD.TcRes.ch715751p.sw
#kc_forall_tree c2p_leaf (fun L => CFSG.KD.TcRes.C2P.leaf L = true) 101
  CFSG.KD.TcRes.ch715751p.leaf

#kc_forall_tree c2m_pos (fun g => CFSG.KD.TcRes.C2M.pos g = true) 240
  CFSG.KD.TcRes.ch715751m.pos
#kc_forall_tree c2m_dec (fun g => CFSG.KD.TcRes.C2M.dec g = true) 240
  CFSG.KD.TcRes.ch715751m.dec
#kc_forall_tree c2m_line (fun i => CFSG.KD.TcRes.C2M.line i = true) 1038
  CFSG.KD.TcRes.ch715751m.line
#kc_forall_tree c2m_leaf (fun L => CFSG.KD.TcRes.C2M.leaf L = true) 101
  CFSG.KD.TcRes.ch715751m.mleaf

#kc_forall_tree c3_gen (fun k => CFSG.KD.TcRes.C3.gen k = true) 3 CFSG.KD.TcRes.ch715752.gen
#kc_forall_tree c3_root (fun k => CFSG.KD.TcRes.C3.root k = true) 4 CFSG.KD.TcRes.ch715752.root
#kc_forall_tree c3_line (fun k => CFSG.KD.TcRes.C3.line k = true) 12 CFSG.KD.TcRes.ch715752.line
#kc_forall_tree c3_leaf (fun L => CFSG.KD.TcRes.C3.leaf L = true) 120
  CFSG.KD.TcRes.ch715752.leaf

end CFSG.KD.TcRes.ch715750all

end
