success p q k = (1 - p) * (1 - q) ** (k - 2) * q

expected d1 d2 = d1 * success (min (d1 * 0.1 + 0.3) 1.0) (d2 * 0.1) 1
                 + sum [ d2 * k * success (min (d1 * 0.1 + 0.3) 1.0) (d2 * 0.1) k | k <- [2..1000] ]
