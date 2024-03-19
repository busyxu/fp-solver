(declare-fun a_ack!52 () (_ BitVec 64))
(declare-fun FPCHECK_FADD_ACCURACY
             ((_ FloatingPoint 11 53) (_ FloatingPoint 11 53))
             Bool)
(declare-fun b_ack!51 () (_ BitVec 64))
(declare-fun CF_cos ((_ BitVec 64)) (_ FloatingPoint 11 53))
(assert (fp.lt (fp.abs ((_ to_fp 11 53) a_ack!52)) ((_ to_fp 11 53) #x3f20000000000000)))
(assert (let ((a!1 (fp.mul roundNearestTiesToEven
                   (fp.mul roundNearestTiesToEven
                           ((_ to_fp 11 53) a_ack!52)
                           (fp.mul roundNearestTiesToEven
                                   ((_ to_fp 11 53) a_ack!52)
                                   ((_ to_fp 11 53) a_ack!52)))
                   (fp.mul roundNearestTiesToEven
                           ((_ to_fp 11 53) a_ack!52)
                           ((_ to_fp 11 53) a_ack!52)))))
  (FPCHECK_FADD_ACCURACY
    (fp.abs (fp.div roundNearestTiesToEven
                    a!1
                    ((_ to_fp 11 53) #x4059000000000000)))
    (fp.abs (fp.mul roundNearestTiesToEven
                    (CF_cos a_ack!52)
                    ((_ to_fp 11 53) b_ack!51))))))
