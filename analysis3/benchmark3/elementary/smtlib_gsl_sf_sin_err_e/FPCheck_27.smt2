(declare-fun a_ack!54 () (_ BitVec 64))
(declare-fun FPCHECK_FMUL_OVERFLOW ((_ BitVec 64) (_ FloatingPoint 11 53)) Bool)
(assert (fp.lt (fp.abs ((_ to_fp 11 53) a_ack!54)) ((_ to_fp 11 53) #x3f20000000000000)))
(assert (let ((a!1 (fp.sub roundNearestTiesToEven
                   ((_ to_fp 11 53) #x3ff0000000000000)
                   (fp.div roundNearestTiesToEven
                           (fp.mul roundNearestTiesToEven
                                   ((_ to_fp 11 53) a_ack!54)
                                   ((_ to_fp 11 53) a_ack!54))
                           ((_ to_fp 11 53) #x4018000000000000)))))
  (FPCHECK_FMUL_OVERFLOW
    #x3cb0000000000000
    (fp.abs (fp.mul roundNearestTiesToEven ((_ to_fp 11 53) a_ack!54) a!1)))))
