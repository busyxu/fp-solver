(declare-fun a_ack!30 () (_ BitVec 64))
(declare-fun FPCHECK_FDIV_OVERFLOW ((_ FloatingPoint 11 53) (_ BitVec 64)) Bool)
(assert (fp.lt (fp.abs ((_ to_fp 11 53) a_ack!30)) ((_ to_fp 11 53) #x3f20000000000000)))
(assert (let ((a!1 (fp.mul roundNearestTiesToEven
                   (fp.mul roundNearestTiesToEven
                           ((_ to_fp 11 53) a_ack!30)
                           (fp.mul roundNearestTiesToEven
                                   ((_ to_fp 11 53) a_ack!30)
                                   ((_ to_fp 11 53) a_ack!30)))
                   (fp.mul roundNearestTiesToEven
                           ((_ to_fp 11 53) a_ack!30)
                           ((_ to_fp 11 53) a_ack!30)))))
  (FPCHECK_FDIV_OVERFLOW a!1 #x4059000000000000)))
