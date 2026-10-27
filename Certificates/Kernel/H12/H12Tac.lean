module

public import CFSG.Quasithin.Background.H12OneHatM22PfInputs
public import CFSG.Certificates.Kernel.H12KSound

public section

namespace CertificateChecks.KernelH12

macro "h12_tac" : tactic => `(tactic| (
  simp only [CFSG.Quasithin.H.Mathieu.H12Cert.zB, CFSG.Quasithin.H.Mathieu.H12Cert.orbB,
    CFSG.Quasithin.H.Mathieu.H12Cert.s0B, CFSG.Quasithin.H.Mathieu.H12Cert.schB,
    CFSG.Quasithin.H.Mathieu.H12Cert.tB, CFSG.Quasithin.H.Mathieu.H12Cert.s0E,
    CFSG.Quasithin.H.Mathieu.H12Cert.s0G, CFSG.Quasithin.H.Mathieu.H12Cert.tE,
    CFSG.Quasithin.H.Mathieu.H12Cert.rE, CFSG.Quasithin.H.Mathieu.H12Cert.rG,
    CFSG.Quasithin.H.Mathieu.H12Cert.y0, CFSG.Quasithin.H.Mathieu.H12Cert.gInv,
    CFSG.Quasithin.H.Mathieu.H12Cert.f0, CFSG.Quasithin.H.Mathieu.H12Cert.lineNe,
    CFSG.Quasithin.H13.MatNCert.subB, CFSG.Quasithin.H13.MatNCert.closedB,
    CFSG.Quasithin.H13.MatNCert.nodupB, CFSG.Quasithin.H13.MatNCert.evalW,
    CFSG.KC.Mat8P.decide_isChain_toP, CFSG.KC.Mat12P.codeL_toQ, CFSG.KC.H12K.orbL_toT,
    CFSG.KC.Mat12P.elemsOf_toQ, CFSG.KC.Mat12P.mulN_toF, CFSG.KC.Mat12P.mvN_toR,
    CFSG.KC.Mat12P.powN_toF,
    CFSG.KC.Mat8P.hs_contains_toLR', CFSG.KC.Mat8P.hs_contains_toLR]
  decide +kernel))

end CertificateChecks.KernelH12

end
