// TODO: write own Sha3 shake
package main
import ("fmt"; "os"; "math/big"; "encoding/hex"; "crypto/sha256"; "crypto/rand";)

func asserteq(a, b *big.Int) bool {
  if a.Cmp(b) != 0 {
    fmt.Printf("Assert failed, a != b: (%x != %x)\n", a, b)
    os.Exit(1)
  }
  return true
}

func inverse_mod(k, p *big.Int) *big.Int {
  if k.Cmp(big.NewInt(0)) == 0 {
    fmt.Println("not good")
    return nil
  } else if k.Sign() == -1 {
  var ktn = new(big.Int)
    ktn = new(big.Int).Mul(k, big.NewInt(-1))
    kt := inverse_mod(ktn, p)
    ret:= new(big.Int).Sub(p, kt)
    return ret
  }
  s, os, t, ot, r, or := big.NewInt(0), big.NewInt(1), big.NewInt(1), big.NewInt(0), p, k
  for r.Cmp(big.NewInt(0)) != 0 {
    q := new(big.Int).Div(or, r)                            // quot = oldr / r
    or, r = r, new(big.Int).Sub(or, new(big.Int).Mul(q, r)) // oldr, r = r, oldr - (quot * r)
    os, s = s, new(big.Int).Sub(os, new(big.Int).Mul(q, s)) // olds, s = s, olds - (quot * s)
    ot, t = t, new(big.Int).Sub(ot, new(big.Int).Mul(q, t)) // oltd, t = t, oldt - (quot * t)
  }                                                         // gcd, x, y = oldr, olds, oldt
  asserteq(or, big.NewInt(1))                               // assert gcd == 1
  kret := new(big.Int).Mod(new(big.Int).Mul(k, os), p)      // (k * x) % p
  asserteq(kret, big.NewInt(1))                             // assert (k * x) % p == 1
  return new(big.Int).Mod(os, p)                            // return (x % p)
}

func point_add(p1x, p1y, p2x, p2y, p *big.Int) (*big.Int, *big.Int) {
  var m = new(big.Int)
  if p1x.Cmp(big.NewInt(0)) == 0 && p1y.Cmp(big.NewInt(0)) == 0 { // if point1 == 0, return point2
    return p2x, p2y
  } else if p2x.Cmp(big.NewInt(0)) == 0 && p2y.Cmp(big.NewInt(0)) == 0 { // if point2 == 0, return point1
    return p1x, p1y
  }
  if p1x.Cmp(p2x) == 0 && p1y.Cmp(p2y) != 0 { // if x1 == x2 and y1 != y2, return 0, 0
    return big.NewInt(0), big.NewInt(0)
  } else if p1x.Cmp(p2x) == 0 { // if x1 == x2, m = (3 * x1 * x2 + curve.a) * inverse_mod(2 * y1, curve.p)
    yy := inverse_mod(new(big.Int).Add(p1y, p1y), p)
    m = new(big.Int).Mul(yy, new(big.Int).Mul(new(big.Int).Add(new(big.Int).Add(p1x, p1x), p1x), p2x))
  } else { // m = (y1 - y2) * inverse_mod(x1 - x2, curve.p)
    m = new(big.Int).Mul(inverse_mod(new(big.Int).Sub(p1x, p2x), p), new(big.Int).Sub(p1y, p2y))
  }
  x3 := new(big.Int).Sub(new(big.Int).Sub(new(big.Int).Mul(m, m), p1x), p2x) // x3 = m * m - x1 - x2
  y3 := new(big.Int).Add(p1y, new(big.Int).Mul(m, new(big.Int).Sub(x3, p1x))) // y3 = y1 + m * (x3 - x1)
  y3n := new(big.Int).Mul(y3, big.NewInt(-1)) // y3 ^= -1
  return new(big.Int).Mod(x3, p), new(big.Int).Mod(y3n, p) // return (x3 % curve.p, -y3 % curve.p)
}

func point_mul(p1x, p1y, p0, p *big.Int) (*big.Int, *big.Int) {
  var k, r1x, r1y, r0x, r0y *big.Int
  k = p0
  r0x, r0y = big.NewInt(0), big.NewInt(0)
  r1x, r1y = p1x, p1y
  for i := p0.BitLen() - 1; i >= 0; i-- {
    kt := new(big.Int).Rsh(k, uint(i)) // k >>= i
    di := new(big.Int).Mod(kt, big.NewInt(2))
    diim := new(big.Int).Mod(new(big.Int).Add(di, big.NewInt(1)), big.NewInt(2))
    if diim.Cmp(big.NewInt(1)) == 0 {
      r1x, r1y = point_add(r0x, r0y, r1x, r1y, p)
    } else {
      r0x, r0y = point_add(r0x, r0y, r1x, r1y, p)
    }
    if di.Cmp(big.NewInt(1)) == 0 {
      r1x, r1y = point_add(r1x, r1y, r1x, r1y, p)
    } else {
      r0x, r0y = point_add(r0x, r0y, r0x, r0y, p)
    }
  }
  return r0x, r0y
}

func scalar_mul(k, p1x, p1y, p, n *big.Int) (*big.Int, *big.Int) {
  ax, ay, kt, rsx, rsy := p1x, p1y, k, big.NewInt(0), big.NewInt(0)
  q := new(big.Int).Mod(kt, n)
  if q.Cmp(big.NewInt(0)) == 0 || p1x.Cmp(big.NewInt(0)) == 0 || p1y.Cmp(big.NewInt(0)) == 0 {
    return big.NewInt(0), big.NewInt(0)
  } else if kt.Cmp(big.NewInt(0)) == 0 {
    return scalar_mul(new(big.Int).Mul(kt, big.NewInt(-1)), p1x, p1y, p, n)
  }
  for i := kt.BitLen() - 1; i >= 0; i-- {
    ktm := new(big.Int).Mod(kt, big.NewInt(2))
    if ktm.Cmp(big.NewInt(1)) == 0 {
      rsx, rsy = point_add(rsx, rsy, ax, ay, p) // add to result
    }
    ax, ay = point_add(ax, ay, ax, ay, p) // double
    kt = new(big.Int).Rsh(kt, 1)
  }
  return rsx, rsy
}

func sign(priv *big.Int, msg string, curveX, curveY, curveN, curveP *big.Int) (*big.Int, *big.Int) {
  var c, d *big.Int
  mx, _ := new(big.Int).SetString("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141", 16)
  mx = new(big.Int).Sub(mx, big.NewInt(1))
  u, _ := rand.Int(rand.Reader, mx)
  h := sha256.New()
  h.Write([]byte(msg))
  hs := h.Sum(nil)
  hash1, _ := new(big.Int).SetString(hex.EncodeToString(hs), 16)
  for {
    vx, _ := point_mul(curveX, curveY, u, curveP) // _ == vy
    c = new(big.Int).Mod(vx, curveN)
    if c.Cmp(big.NewInt(0)) == 0 {
      continue
    }
    mi := inverse_mod(u, curveN)
    hc := new(big.Int).Mul(priv, c)
    hh := new(big.Int).Add(hash1, hc)
    mc := new(big.Int).Mul(mi, hh)
    d = new(big.Int).Mod(mc, curveN)
    if d.Cmp(big.NewInt(0)) == 0 {
      continue
    }
    break
  }
  return c, d
}

func verify(msg string, pubx, puby, sigx, sigy, curveX, curveY, curveP, curveN *big.Int) *big.Int {
  h := sha256.New()
  h.Write([]byte(msg))
  hs := h.Sum(nil)
  hash1, _ := new(big.Int).SetString(hex.EncodeToString(hs), 16)
  hh := inverse_mod(sigy, curveN)
  ht := new(big.Int).Mul(hash1, hh)
  h1 := new(big.Int).Mod(ht, curveN)
  ht  = new(big.Int).Mul(sigx, hh)
  h2 := new(big.Int).Mod(ht, curveN)
  h1x, h1y := scalar_mul(h1, curveX, curveY, curveP, curveN)
  h2x, h2y := scalar_mul(h2, pubx, puby, curveP, curveN) 
  px, _ := point_add(h1x, h1y, h2x, h2y, curveP) // _ == py
  c1 := new(big.Int).Mod(px, curveN)
  return big.NewInt(int64(c1.Cmp(sigx))) // return 0 if true
}

func genkeypair(curveX, curveY, curveP, curveN *big.Int) (*big.Int, *big.Int, *big.Int) {
  mx, _ := new(big.Int).SetString("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141", 16)
  mx = new(big.Int).Sub(mx, big.NewInt(1))
  sec, _ := rand.Int(rand.Reader, mx)
  pubx, puby := scalar_mul(sec, curveX, curveY, curveP, curveN)
  return pubx, puby, sec
}

func gensharedsecret(sec, pubx, puby, curveP, curveN *big.Int) (*big.Int, *big.Int) {
  return scalar_mul(sec, pubx, puby, curveP, curveN)
}

func verifysharedsecret(alshrx, alshry, boshrx, boshry, alpriv, bopriv, curveX, curveY, curveP, curveN *big.Int) *big.Int {
  if alshrx.Cmp(boshrx) != 0 || alshry.Cmp(boshry) != 0 {
    return big.NewInt(1) // false
  }
  s := new(big.Int).Mul(alpriv, bopriv)
  t := new(big.Int).Mod(s, curveN)
  r1, _:= scalar_mul(t, curveX, curveY, curveP, curveN)
  if r1.Cmp(alshrx) != 0 {
    return big.NewInt(1) // false
  }
  return big.NewInt(0) // true
}

func main() {
  for i := 0; i < 1000; i++ {
    // var curveA = big.NewInt(0)
    // var curveB = big.NewInt(7)
    // var curveH = big.NewInt(1)
    var curveN, _ = new(big.Int).SetString("fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141", 16)
    var curveP, _ = new(big.Int).SetString("fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f", 16)
    var curveX, _ = new(big.Int).SetString("79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798", 16)
    var curveY, _ = new(big.Int).SetString("483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8", 16)

    var alpubx, alpuby, alpriv = genkeypair(curveX, curveY, curveP, curveN) // alices keypair
    var bopubx, bopuby, bopriv = genkeypair(curveX, curveY, curveP, curveN) // bobs keypair

    var alshrx, alshry = gensharedsecret(bopriv, alpubx, alpuby, curveP, curveN) // alices shared secret
    var boshrx, boshry = gensharedsecret(alpriv, bopubx, bopuby, curveP, curveN) // bobs shared secret

    asserteq(verifysharedsecret(alshrx, alshry, boshrx, boshry, alpriv, bopriv, curveX, curveY, curveP, curveN), big.NewInt(0))
    bosigx, bosigy := sign(bopriv, "hai wurld", curveX, curveY, curveN, curveP) // create bobs signature
    alsigx, alsigy := sign(alpriv, "bai wurld", curveX, curveY, curveN, curveP) // create alices signature
    asserteq(verify("hai wurld", bopubx, bopuby, bosigx, bosigy, curveX, curveY, curveP, curveN), big.NewInt(0))
    asserteq(verify("bai wurld", alpubx, alpuby, alsigx, alsigy, curveX, curveY, curveP, curveN), big.NewInt(0))
  }
  fmt.Println("ok")
}

