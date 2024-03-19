(declare-fun a_ack!80 () (_ BitVec 64))
(declare-fun CF_floor ((_ FloatingPoint 11 53)) (_ FloatingPoint 11 53))
(declare-fun FPCHECK_FMUL_OVERFLOW ((_ FloatingPoint 11 53) (_ BitVec 64)) Bool)
(assert (not (fp.lt (fp.abs ((_ to_fp 11 53) a_ack!80))
            ((_ to_fp 11 53) #x3f20000000000000))))
(assert (let ((a!1 (CF_floor (fp.div roundNearestTiesToEven
                             (fp.abs ((_ to_fp 11 53) a_ack!80))
                             ((_ to_fp 11 53) #x3fe921fb54442d18)))))
(let ((a!2 (bvand ((_ fp.to_sbv 32)
                    roundTowardZero
                    (fp.sub roundNearestTiesToEven
                            a!1
                            ((_ to_fp 11 53) #x7fe45f306dc9c882)))
                  #x00000001)))
  (= #x00000000 a!2))))
(assert (let ((a!1 (CF_floor (fp.div roundNearestTiesToEven
                             (fp.abs ((_ to_fp 11 53) a_ack!80))
                             ((_ to_fp 11 53) #x3fe921fb54442d18)))))
(let ((a!2 (bvslt #x00000003
                  ((_ fp.to_sbv 32)
                    roundTowardZero
                    (fp.sub roundNearestTiesToEven
                            a!1
                            ((_ to_fp 11 53) #x7fe45f306dc9c882))))))
  (not a!2))))
(assert (let ((a!1 (CF_floor (fp.div roundNearestTiesToEven
                             (fp.abs ((_ to_fp 11 53) a_ack!80))
                             ((_ to_fp 11 53) #x3fe921fb54442d18)))))
  (FPCHECK_FMUL_OVERFLOW a!1 #x3fe921fb40000000)))
