module

public import CFSG.Quasithin.H13.L32NM22Inputs
public import CFSG.Certificates.Kernel.M22KSound

public section

namespace CertificateChecks.KernelH13

macro "m22_tac" : tactic => `(tactic| (
  simp only [CFSG.Quasithin.H13.M22Cert.orbB, CFSG.Quasithin.H13.M22Cert.s0B,
    CFSG.Quasithin.H13.M22Cert.schB, CFSG.Quasithin.H13.M22Cert.pB,
    CFSG.Quasithin.H13.M22Cert.e0B, CFSG.Quasithin.H13.M22Cert.witB,
    CFSG.Quasithin.H13.M22Cert.ovB, CFSG.Quasithin.H13.M22Cert.oB,
    CFSG.Quasithin.H13.M22Cert.m12B, CFSG.Quasithin.H13.M22Cert.s0E,
    CFSG.Quasithin.H13.M22Cert.s0G, CFSG.Quasithin.H13.M22Cert.pE,
    CFSG.Quasithin.H13.M22Cert.e0E, CFSG.Quasithin.H13.M22Cert.cjL,
    CFSG.Quasithin.H13.M22Cert.mE, CFSG.Quasithin.H13.M22Cert.mRep,
    CFSG.Quasithin.H13.M22Cert.oE, CFSG.Quasithin.H13.M22Cert.oddOf,
    CFSG.Quasithin.H13.M22Cert.twoOf, CFSG.Quasithin.H13.M22Cert.m12E,
    CFSG.Quasithin.H13.M22Cert.m12G, CFSG.Quasithin.H13.M22Cert.gInv,
    CFSG.Quasithin.H13.MatNCert.subB, CFSG.Quasithin.H13.MatNCert.closedB,
    CFSG.Quasithin.H13.MatNCert.nodupB, CFSG.Quasithin.H13.MatNCert.evalW,
    CFSG.Quasithin.H13.MatNCert.polN, CFSG.Quasithin.H13.MatNCert.quadN,
    CFSG.Quasithin.H13.MatNCert.blkInvB, CFSG.Quasithin.H13.MatNCert.blkPerm,
    CFSG.Quasithin.H13.MatNCert.blkOf,
    CFSG.KC.Mat8P.decide_isChain_toP, CFSG.KC.Mat12P.codeL_toQ, CFSG.KC.M22K.orbL_toT,
    CFSG.KC.Mat12P.elemsOf_toQ, CFSG.KC.Mat12P.mulN_toF, CFSG.KC.Mat12P.mvN_toR,
    CFSG.KC.Mat12P.powN_toF, CFSG.KC.Mat12P.sqN_toF,
    CFSG.KC.Mat8P.hs_contains_toLR', CFSG.KC.Mat8P.hs_contains_toLR]
  decide +kernel))

end CertificateChecks.KernelH13

end
