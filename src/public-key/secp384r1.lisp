;;;; secp384r1.lisp -- secp384r1 (a.k.a. NIST P-384) elliptic curve

(in-package :crypto)

;;; class definitions
(defclass secp384r1-public-key ()
  ((y :initarg :y :reader secp384r1-key-y :type (simple-array (unsigned-byte 8) (*)))))

(defclass secp384r1-private-key ()
  ((x :initarg :x :reader secp384r1-key-x :type (simple-array (unsigned-byte 8) (*)))
   (y :initarg :y :reader secp384r1-key-y :type (simple-array (unsigned-byte 8) (*)))))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defclass secp384r1-point ()
    ;; Internally, a point (x, y) is represented using the Jacobian projective
    ;; coordinates (X, Y, Z), with x = X / Z^2 and y = Y / Z^3.
    ((x :initarg :x :type integer)
     (y :initarg :y :type integer)
     (z :initarg :z :type integer)))
  (defmethod make-load-form ((p secp384r1-point) &optional env)
    (declare (ignore env))
    (make-load-form-saving-slots p)))

;;; constant and function definitions
(defconstant +secp384r1-bits+ 384)
(defconstant +secp384r1-p+ 39402006196394479212279040100143613805079739270465446667948293404245721771496870329047266088258938001861606973112319)
(defconstant +secp384r1-b+ 27580193559959705877849011840389048093056905856361568521428707301988689241309860865136260764883745107765439761230575)
(defconstant +secp384r1-l+ 39402006196394479212279040100143613805079739270465446667946905279627659399113263569398956308152294913554433653942643)
(defconstant +secp384r1-i+ 29551504647295859409209280075107710353809804452849085000961220053184291328622652746785449566194203501396205229834239)

(defconst +secp384r1-g+
  (make-instance 'secp384r1-point
    :x 26247035095799689268623156744566981891852923491109213387815615900925518854738050089022388053975719786650872476732087
    :y 8325710961489029985546751289520108179287853048861315594709205902480503199884419224438643760392947333078086511627871
    :z 1))
(defconst +secp384r1-point-at-infinity+
  (make-instance 'secp384r1-point :x 1 :y 1 :z 0))

(defmethod ec-scalar-inv ((kind (eql :secp384r1)) n)
  (expt-mod n (- +secp384r1-p+ 2) +secp384r1-p+))

(defmethod ec-point-equal ((p secp384r1-point) (q secp384r1-point))
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 0)))
  (with-slots ((x1 x) (y1 y) (z1 z)) p
    (declare (type integer x1 y1 z1))
    (with-slots ((x2 x) (y2 y) (z2 z)) q
      (declare (type integer x2 y2 z2))
      (let ((z1z1 (mod (* z1 z1) +secp384r1-p+))
            (z2z2 (mod (* z2 z2) +secp384r1-p+)))
        (and (zerop (mod (- (* x1 z2z2) (* x2 z1z1)) +secp384r1-p+))
             (zerop (mod (- (* y1 z2z2 z2) (* y2 z1z1 z1)) +secp384r1-p+)))))))

(defmethod ec-double ((p secp384r1-point))
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 0)))
  (with-slots ((x1 x) (y1 y) (z1 z)) p
    (declare (type integer x1 y1 z1))
    (if (zerop z1)
        +secp384r1-point-at-infinity+
        (let* ((xx (mod (* x1 x1) +secp384r1-p+))
               (yy (mod (* y1 y1) +secp384r1-p+))
               (yyyy (mod (* yy yy) +secp384r1-p+))
               (zz (mod (* z1 z1) +secp384r1-p+))
               (x1+yy (mod (+ x1 yy) +secp384r1-p+))
               (y1+z1 (mod (+ y1 z1) +secp384r1-p+))
               (s (mod (* 2 (- (* x1+yy x1+yy) xx yyyy)) +secp384r1-p+))
               (m (mod (* 3 (- xx (* zz zz))) +secp384r1-p+))
               (u (mod (- (* m m) (* 2 s)) +secp384r1-p+))
               (x2 u)
               (y2 (mod (- (* m (- s u)) (* 8 yyyy)) +secp384r1-p+))
               (z2 (mod (- (* y1+z1 y1+z1) yy zz) +secp384r1-p+)))
          (make-instance 'secp384r1-point :x x2 :y y2 :z z2)))))

(defmethod ec-add ((p secp384r1-point) (q secp384r1-point))
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 0)))
  (with-slots ((x1 x) (y1 y) (z1 z)) p
    (declare (type integer x1 y1 z1))
    (with-slots ((x2 x) (y2 y) (z2 z)) q
      (declare (type integer x2 y2 z2))
      (cond
        ((zerop z1)
         q)
        ((zerop z2)
         p)
        (t
         (let* ((z1z1 (mod (* z1 z1) +secp384r1-p+))
                (z2z2 (mod (* z2 z2) +secp384r1-p+))
                (u1 (mod (* x1 z2z2) +secp384r1-p+))
                (u2 (mod (* x2 z1z1) +secp384r1-p+))
                (s1 (mod (* y1 z2 z2z2) +secp384r1-p+))
                (s2 (mod (* y2 z1 z1z1) +secp384r1-p+)))
           (if (= u1 u2)
               (if (= s1 s2)
                   (ec-double p)
                   +secp384r1-point-at-infinity+)
               (let* ((h (mod (- u2 u1) +secp384r1-p+))
                      (i (mod (* 4 h h) +secp384r1-p+))
                      (j (mod (* h i) +secp384r1-p+))
                      (r (mod (* 2 (- s2 s1)) +secp384r1-p+))
                      (v (mod (* u1 i) +secp384r1-p+))
                      (x3 (mod (- (* r r) j (* 2 v)) +secp384r1-p+))
                      (y3 (mod (- (* r (- v x3)) (* 2 s1 j)) +secp384r1-p+))
                      (z1+z2 (mod (+ z1 z2) +secp384r1-p+))
                      (z3 (mod (* (- (* z1+z2 z1+z2) z1z1 z2z2) h) +secp384r1-p+)))
                 (make-instance 'secp384r1-point :x x3 :y y3 :z z3)))))))))

(defmethod ec-scalar-mult ((p secp384r1-point) e)
  ;; Point multiplication on NIST P-384 curve using the Montgomery ladder.
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 0))
           (type integer e))
  (do ((r0 +secp384r1-point-at-infinity+)
       (r1 p)
       (i (1- +secp384r1-bits+) (1- i)))
      ((minusp i) r0)
    (declare (type secp384r1-point r0 r1)
             (type fixnum i))
    (if (logbitp i e)
        (setf r0 (ec-add r0 r1)
              r1 (ec-double r1))
        (setf r1 (ec-add r0 r1)
              r0 (ec-double r0)))))

(defmethod ec-point-on-curve-p ((p secp384r1-point))
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 0)))
  (with-slots (x y z) p
    (declare (type integer x y z))
    (let* ((y2 (mod (* y y) +secp384r1-p+))
           (x3 (mod (* x x x) +secp384r1-p+))
           (z2 (mod (* z z) +secp384r1-p+))
           (z4 (mod (* z2 z2) +secp384r1-p+))
           (z6 (mod (* z4 z2) +secp384r1-p+))
           (a (mod (+ x3 (* -3 x z4) (* +secp384r1-b+ z6)) +secp384r1-p+)))
      (declare (type integer y2 x3 z2 z4 z6 a))
      (zerop (mod (- y2 a) +secp384r1-p+)))))

(defmethod ec-make-point ((kind (eql :secp384r1)) &key x y)
  (unless x
    (error 'missing-point-parameter
           :kind 'secp384r1
           :parameter 'x
           :description "coordinate"))
  (unless y
    (error 'missing-point-parameter
           :kind 'secp384r1
           :parameter 'y
           :description "coordinate"))
  (let ((p (make-instance 'secp384r1-point :x x :y y :z 1)))
    (if (ec-point-on-curve-p p)
        p
        (error 'invalid-curve-point :kind 'secp384r1))))

(defmethod ec-destructure-point ((p secp384r1-point))
  (with-slots (x y z) p
    (declare (type integer x y z))
    (when (zerop z)
      (error 'ironclad-error
             :format-control "The point at infinity can't be encoded."))
    (let* ((invz (ec-scalar-inv :secp384r1 z))
           (invz2 (mod (* invz invz) +secp384r1-p+))
           (invz3 (mod (* invz2 invz) +secp384r1-p+))
           (x (mod (* x invz2) +secp384r1-p+))
           (y (mod (* y invz3) +secp384r1-p+)))
      (list :x x :y y))))

(defmethod ec-encode-scalar ((kind (eql :secp384r1)) n)
  (integer-to-octets n :n-bits +secp384r1-bits+ :big-endian t))

(defmethod ec-decode-scalar ((kind (eql :secp384r1)) octets)
  (octets-to-integer octets :big-endian t))

(defmethod ec-encode-point ((p secp384r1-point))
  (let* ((coordinates (ec-destructure-point p))
         (x (getf coordinates :x))
         (y (getf coordinates :y)))
    (concatenate '(simple-array (unsigned-byte 8) (*))
                 (vector 4)
                 (ec-encode-scalar :secp384r1 x)
                 (ec-encode-scalar :secp384r1 y))))

(defmethod ec-decode-point ((kind (eql :secp384r1)) octets)
  (case (aref octets 0)
    ((2 3)
     ;; Compressed point
     (if (= (length octets) (1+ (/ +secp384r1-bits+ 8)))
         (let* ((x-bytes (subseq octets 1 (1+ (/ +secp384r1-bits+ 8))))
                (x (ec-decode-scalar :secp384r1 x-bytes))
                (y-sign (- (aref octets 0) 2))
                (y2 (mod (+ (* x x x) (* -3 x) +secp384r1-b+) +secp384r1-p+))
                (y (expt-mod y2 +secp384r1-i+ +secp384r1-p+))
                (y (if (= (logand y 1) y-sign) y (- +secp384r1-p+ y))))
           (ec-make-point :secp384r1 :x x :y y))
         (error 'invalid-curve-point :kind 'secp384r1)))
    ((4)
     ;; Uncompressed point
     (if (= (length octets) (1+ (/ +secp384r1-bits+ 4)))
         (let* ((x-bytes (subseq octets 1 (1+ (/ +secp384r1-bits+ 8))))
                (x (ec-decode-scalar :secp384r1 x-bytes))
                (y-bytes (subseq octets (1+ (/ +secp384r1-bits+ 8))))
                (y (ec-decode-scalar :secp384r1 y-bytes)))
           (ec-make-point :secp384r1 :x x :y y))
         (error 'invalid-curve-point :kind 'secp384r1)))
    (t
     (error 'invalid-curve-point :kind 'secp384r1))))

(defun secp384r1-public-key (sk)
  (let ((a (ec-decode-scalar :secp384r1 sk)))
    (ec-encode-point (ec-scalar-mult +secp384r1-g+ a))))

(defmethod make-signature ((kind (eql :secp384r1)) &key r s &allow-other-keys)
  (unless r
    (error 'missing-signature-parameter
           :kind 'secp384r1
           :parameter 'r
           :description "first signature element"))
  (unless s
    (error 'missing-signature-parameter
           :kind 'secp384r1
           :parameter 's
           :description "second signature element"))
  (concatenate '(simple-array (unsigned-byte 8) (*)) r s))

(defmethod destructure-signature ((kind (eql :secp384r1)) signature)
  (let ((length (length signature)))
    (if (/= length (/ +secp384r1-bits+ 4))
        (error 'invalid-signature-length :kind 'secp384r1)
        (let* ((middle (/ length 2))
               (r (subseq signature 0 middle))
               (s (subseq signature middle)))
          (list :r r :s s)))))

(defmethod generate-signature-nonce ((key secp384r1-private-key) message &optional parameters)
  (declare (ignore key message parameters))
  (or *signature-nonce-for-test*
      (1+ (strong-random (1- +secp384r1-l+)))))

;;; Note that hashing is not performed here.
(defmethod sign-message ((key secp384r1-private-key) message &key (start 0) end &allow-other-keys)
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 0)))
  (let* ((end (min (or end (length message)) (/ +secp384r1-bits+ 8)))
         (sk (ec-decode-scalar :secp384r1 (secp384r1-key-x key)))
         (k (generate-signature-nonce key message))
         (invk (modular-inverse-with-blinding k +secp384r1-l+))
         (r (ec-scalar-mult +secp384r1-g+ k))
         (x (subseq (ec-encode-point r) 1 (1+ (/ +secp384r1-bits+ 8))))
         (r (ec-decode-scalar :secp384r1 x))
         (r (mod r +secp384r1-l+))
         (h (subseq message start end))
         (e (ec-decode-scalar :secp384r1 h))
         (s (mod (* invk (+ e (* sk r))) +secp384r1-l+)))
    (if (not (or (zerop r) (zerop s)))
        (make-signature :secp384r1
                        :r (ec-encode-scalar :secp384r1 r)
                        :s (ec-encode-scalar :secp384r1 s))
        (sign-message key message :start start :end end))))

(defmethod verify-signature ((key secp384r1-public-key) message signature &key (start 0) end &allow-other-keys)
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 0)))
  (unless (= (length signature) (/ +secp384r1-bits+ 4))
    (error 'invalid-signature-length :kind 'secp384r1))
  (let* ((end (min (or end (length message)) (/ +secp384r1-bits+ 8)))
         (pk (ec-decode-point :secp384r1 (secp384r1-key-y key)))
         (signature-elements (destructure-signature :secp384r1 signature))
         (r (ec-decode-scalar :secp384r1 (getf signature-elements :r)))
         (s (ec-decode-scalar :secp384r1 (getf signature-elements :s)))
         (h (subseq message start end))
         (e (ec-decode-scalar :secp384r1 h))
         (w (modular-inverse-with-blinding s +secp384r1-l+))
         (u1 (mod (* e w) +secp384r1-l+))
         (u2 (mod (* r w) +secp384r1-l+))
         (rp (ec-add (ec-scalar-mult +secp384r1-g+ u1)
                     (ec-scalar-mult pk u2)))
         (x (subseq (ec-encode-point rp) 1 (1+ (/ +secp384r1-bits+ 8))))
         (v (ec-decode-scalar :secp384r1 x))
         (v (mod v +secp384r1-l+)))
    (and (< r +secp384r1-l+)
         (< s +secp384r1-l+)
         (= v r))))

(defmethod make-public-key ((kind (eql :secp384r1)) &key y &allow-other-keys)
  (unless y
    (error 'missing-key-parameter
           :kind 'secp384r1
           :parameter 'y
           :description "public key"))
  (make-instance 'secp384r1-public-key :y y))

(defmethod destructure-public-key ((public-key secp384r1-public-key))
  (list :y (secp384r1-key-y public-key)))

(defmethod make-private-key ((kind (eql :secp384r1)) &key x y &allow-other-keys)
  (unless x
    (error 'missing-key-parameter
           :kind 'secp384r1
           :parameter 'x
           :description "private key"))
  (make-instance 'secp384r1-private-key :x x :y (or y (secp384r1-public-key x))))

(defmethod destructure-private-key ((private-key secp384r1-private-key))
  (list :x (secp384r1-key-x private-key)
        :y (secp384r1-key-y private-key)))

(defmethod generate-key-pair ((kind (eql :secp384r1)) &key &allow-other-keys)
  (let* ((sk (ec-encode-scalar :secp384r1 (1+ (strong-random (1- +secp384r1-l+)))))
         (pk (secp384r1-public-key sk)))
    (values (make-private-key :secp384r1 :x sk :y pk)
            (make-public-key :secp384r1 :y pk))))

(defmethod diffie-hellman ((private-key secp384r1-private-key) (public-key secp384r1-public-key))
  (let ((s (ec-decode-scalar :secp384r1 (secp384r1-key-x private-key)))
        (p (ec-decode-point :secp384r1 (secp384r1-key-y public-key))))
    (ec-encode-point (ec-scalar-mult p s))))
