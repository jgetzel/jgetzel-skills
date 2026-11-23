import LSql.Num

/-! Tests for LSql.Num. Every expected value was produced by the real sqlite3 3.54.0 (random and edge
inputs, compared one by one before being frozen here); the few return-code checks marked as derived
come from reading util.c. -/

open LSql LSql.Num

private def hexOf (b : ByteArray) : String :=
  b.foldl (fun s c => s ++ String.ofList (Nat.toDigits 16 (c.toNat / 16)) ++ String.ofList (Nat.toDigits 16 (c.toNat % 16))) ""

private def showV : Value → String
  | .null => "null:"
  | .int i => "integer:" ++ int64ToText i
  | .real f => "real:" ++ fmtReal f
  | .text s => "text:" ++ s
  | .blob b => "blob:" ++ hexOf b

private def numStr (s : String) : String :=
  match textToNumeric? s with | some v => showV v | none => "text:" ++ s

private def realStr (s : String) : String :=
  match textToReal? s with | some f => "real:" ++ fmtReal f | none => "text:" ++ s

private def cnStr (s : String) : String := showV (castToNumeric (.text s))
private def nvStr (s : String) : String := showV (numericValue (.text s))

private def cmpI (i : Int64) (b : UInt64) : Int :=
  match compareIntReal i (Float.ofBits b) with | .lt => -1 | .eq => 0 | .gt => 1

private def arithStr : Option Int64 → String
  | some v => toString v.toInt
  | none => "none"

private def pfHex (f : String) (a : List Value) : String :=
  hexOf ((printfBytes? f.toUTF8 a.toArray).getD ByteArray.empty)

/-! ### Integers to text -/
#guard int64ToText 0 == "0"
#guard int64ToText (-1) == "-1"
#guard int64ToText 1234567890123456789 == "1234567890123456789"
#guard int64ToText Int64.maxValue == "9223372036854775807"
#guard int64ToText Int64.minValue == "-9223372036854775808"
#guard int64ToText 10 == "10"
#guard int64ToText 100000 == "100000"

/-! ### Return codes (derived from util.c) -/
#guard (atoF "").rc == 0
#guard (atoF "abc").rc == 0
#guard (atoF "0").rc == 5
#guard (atoF " 12 ").rc == 1
#guard (atoF "1.5").rc == 3
#guard (atoF ".5").rc == 3
#guard (atoF "1e5").rc == 3
#guard (atoF "12abc").rc == -15
#guard (atoF "1e").rc == -15
#guard (atoF "1.5x").rc == -13
#guard (atoF "5").isInteger && !(atoF "5.0").isInteger
#guard (atoF "12abc").kind == .trailing && (atoF "12").kind == .whole && (atoF "x").kind == .invalid
#guard (atoi64 "").rc == -1
#guard (atoi64 "abc").rc == -1
#guard (atoi64 "000").rc == 0
#guard (atoi64 "12").rc == 0
#guard (atoi64 " 12 ").rc == 0
#guard (atoi64 "12x").rc == 1
#guard (atoi64 "9223372036854775807").rc == 0
#guard (atoi64 "9223372036854775808").rc == 3
#guard (atoi64 "-9223372036854775808").rc == 0
#guard (atoi64 "9223372036854775809").rc == 2
#guard (atoi64 "99999999999999999999").rc == 2
#guard (atoi64 "-99999999999999999999").value == Int64.minValue

/-! ### Arithmetic corner cases -/
#guard addInt? Int64.maxValue 1 == none
#guard addInt? Int64.minValue (-1) == none
#guard subInt? Int64.minValue 1 == none
#guard subInt? 0 Int64.minValue == none
#guard mulInt? Int64.minValue (-1) == none
#guard divInt? Int64.minValue (-1) == none
#guard divInt? 5 0 == none
#guard remInt? 5 0 == none
#guard remInt? Int64.minValue (-1) == some 0
#guard remInt? (-7) 3 == some (-1)
#guard divInt? (-7) 2 == some (-3)
example : addInt? 2 3 = some 5 := by decide

/-! ### fmtReal (printf "%!.17g") -/
#guard fmtReal (Float.ofBits 0x3fb999999999999a) == "0.1"
#guard fmtReal (Float.ofBits 0x3fd5555555555555) == "0.33333333333333332"
#guard fmtReal (Float.ofBits 0x4008000000000000) == "3.0"
#guard fmtReal (Float.ofBits 0x4415af1d78b58c40) == "1.0e+20"
#guard fmtReal (Float.ofBits 0x7e6ddd4baa009303) == "1.0e+301"
#guard fmtReal (Float.ofBits 0x3e90c6f7a0b5ed8d) == "2.5e-07"
#guard fmtReal (Float.ofBits 0x437b69b4ba630f35) == "1.2345678901234568e+17"
#guard fmtReal (Float.ofBits 0x3fd3333333333334) == "0.30000000000000004"
#guard fmtReal (Float.ofBits 0x7ff0000000000000) == "Inf"
#guard fmtReal (Float.ofBits 0xfff0000000000000) == "-Inf"
#guard fmtReal (Float.ofBits 0x8000000000000000) == "0.0"
#guard fmtReal (Float.ofBits 0x0000000000000001) == "4.9406564584124654e-324"
#guard fmtReal (Float.ofBits 0x7fefffffffffffff) == "1.7976931348623157e+308"
#guard fmtReal (Float.ofBits 0x0010000000000000) == "2.2250738585072014e-308"
#guard fmtReal (Float.ofBits 0x4340000000000000) == "9007199254740992.0"
#guard fmtReal (Float.ofBits 0x4340000000000000) == "9007199254740992.0"
#guard fmtReal (Float.ofBits 0x433fffffffffffff) == "9007199254740991.0"
#guard fmtReal (Float.ofBits 0x4330000000000001) == "4503599627370497.0"
#guard fmtReal (Float.ofBits 0x4048bc28f5c28f5c) == "49.47"
#guard fmtReal (Float.ofBits 0x430c6bf526340000) == "1000000000000000.0"
#guard fmtReal (Float.ofBits 0x4341c37937e08000) == "10000000000000000.0"
#guard fmtReal (Float.ofBits 0x4376345785d8a000) == "1.0e+17"
#guard fmtReal (Float.ofBits 0x4480f0cf064dd592) == "1.0e+22"
#guard fmtReal (Float.ofBits 0x44b52d02c7e14af6) == "1.0e+23"
#guard fmtReal (Float.ofBits 0x40fe240c9fbe76c9) == "123456.789"
#guard fmtReal (Float.ofBits 0x4059000000000000) == "100.0"
#guard fmtReal (Float.ofBits 0x3ff0000000000000) == "1.0"
#guard fmtReal (Float.ofBits 0xbff0000000000000) == "-1.0"
#guard fmtReal (Float.ofBits 0x3fe0000000000000) == "0.5"
#guard fmtReal (Float.ofBits 0x3ee4f8b588e368f1) == "1.0e-05"
#guard fmtReal (Float.ofBits 0x3f1a36e2eb1c432d) == "0.0001"
#guard fmtReal (Float.ofBits 0x3f202c9dedbc309d) == "0.0001234"
#guard fmtReal (Float.ofBits 0x43e56a95319d63e1) == "1.2345678901234567e+19"
#guard fmtReal (Float.ofBits 0x3fd3333333333333) == "0.3"
#guard fmtReal (Float.ofBits 0x4005666666666666) == "2.675"
#guard fmtReal (Float.ofBits 0x3ff0147ae147ae14) == "1.005"
#guard fmtReal (Float.ofBits 0x3f0a36e2eb1c432d) == "5.0e-05"
#guard fmtReal (Float.ofBits 0x401c000000000000) == "7.0"
#guard fmtReal (Float.ofBits 0x54b249ad2594c37d) == "1.0e+100"
#guard fmtReal (Float.ofBits 0x2b2bff2ee48e0530) == "1.0e-100"
#guard fmtReal (Float.ofBits 0x447c7e83209e90b2) == "8.41e+21"
#guard fmtReal (Float.ofBits 0x4011666666666666) == "4.35"
#guard fmtReal (Float.ofBits 0x3fb1eb851eb851ec) == "0.07"
#guard fmtReal (Float.ofBits 0x3ff199999999999a) == "1.1"
#guard fmtReal (Float.ofBits 0x400199999999999a) == "2.2"
#guard fmtReal (Float.ofBits 0x400a666666666666) == "3.3"
#guard fmtReal (Float.ofBits 0x401199999999999a) == "4.4"
#guard fmtReal (Float.ofBits 0x4016000000000000) == "5.5"
#guard fmtReal (Float.ofBits 0x4023e66666666666) == "9.95"
#guard fmtReal (Float.ofBits 0x4058ff5c28f5c28f) == "99.99"
#guard fmtReal (Float.ofBits 0x3fefffffffffffff) == "0.99999999999999989"
#guard fmtReal (Float.ofBits 0x44b52d02c7e14af6) == "1.0e+23"
#guard fmtReal (Float.ofBits 0xc0c0d2981cd8a3e2) == "-8613.1883803177079"
#guard fmtReal (Float.ofBits 0xb5e50636cf899afb) == "-4.495434975017716e-49"
#guard fmtReal (Float.ofBits 0x9cae1fb2139dbfce) == "-1.5589865956406036e-170"
#guard fmtReal (Float.ofBits 0xecf37c12b6b7737b) == "-6.716913253290848e+216"
#guard fmtReal (Float.ofBits 0xe9f682b2e113c04c) == "-2.7569129605037017e+202"
#guard fmtReal (Float.ofBits 0xf0ce028ad5044baa) == "-2.3854571871217986e+235"
#guard fmtReal (Float.ofBits 0xe7a5eb44918f3d57) == "-1.9532071180138707e+191"
#guard fmtReal (Float.ofBits 0xd94b442d40def9f5) == "-1.4081687981410632e+122"
#guard fmtReal (Float.ofBits 0x7894f6fa5c5cf5f3) == "7.0883627781341689e+272"
#guard fmtReal (Float.ofBits 0x1515cecaf5a5a92e) == "4.2453601315769246e-207"
#guard fmtReal (Float.ofBits 0x0a9afce7d14f4b6c) == "1.4042130661091069e-257"
#guard fmtReal (Float.ofBits 0x942cbe4f2470469c) == "-1.7076195638181786e-211"
#guard fmtReal (Float.ofBits 0x7ab9972ae8e02267) == "1.4864649986439781e+283"
#guard fmtReal (Float.ofBits 0x173dfc91bafe1c51) == "1.0028824967950836e-196"
#guard fmtReal (Float.ofBits 0x98efcf267766c535) == "-1.4278586295184176e-188"
#guard fmtReal (Float.ofBits 0x5ad3d4492703282b) == "3.4362460112224466e+129"
#guard fmtReal (Float.ofBits 0xa737078380a2d3bc) == "-8.9183275848325067e-120"
#guard fmtReal (Float.ofBits 0x9e632dd9a4e9fe8b) == "-2.6644073315168857e-162"
#guard fmtReal (Float.ofBits 0x254e396204095b1a) == "5.4503700740143166e-129"
#guard fmtReal (Float.ofBits 0xc7582be36e6f10e4) == "-5.0202114875322093e+35"
#guard fmtReal (Float.ofBits 0x5a91f54c22665f6d) == "1.9450053673652873e+128"
#guard fmtReal (Float.ofBits 0xa8e812f623ba27bd) == "-1.2512990230872623e-111"
#guard fmtReal (Float.ofBits 0x7c0f9f4bfbb24d49) == "3.8521098350801356e+289"
#guard fmtReal (Float.ofBits 0x40851154318f09c0) == "674.1661101507998"
#guard fmtReal (Float.ofBits 0x51d8f1e6073e1803) == "1.9383885090833646e+86"
#guard fmtReal (Float.ofBits 0x652ec8682ec101e1) == "2.4948021990800074e+179"
#guard fmtReal (Float.ofBits 0x8c79d47f94a55fac) == "-1.4430759947926331e-248"
#guard fmtReal (Float.ofBits 0x8cbd8dc21275cfd1) == "-2.6417764156468506e-247"
#guard fmtReal (Float.ofBits 0x6c40478c0346449e) == "2.7402329001742723e+213"
#guard fmtReal (Float.ofBits 0x611160784146ea45) == "3.8172305879791515e+159"
#guard fmtReal (Float.ofBits 0xf6267376c4ab57ee) == "-1.3807738317040906e+261"
#guard fmtReal (Float.ofBits 0x2d99d73ca052d70b) == "5.0741899767275377e-89"
#guard fmtReal (Float.ofBits 0x926e63f1ba00ec30) == "-6.7258890291445787e-220"
#guard fmtReal (Float.ofBits 0x435112c6399ba2e7) == "19222868733627292.0"
#guard fmtReal (Float.ofBits 0x0f532f9d58ff3d51) == "7.5427152133598363e-235"
#guard fmtReal (Float.ofBits 0x328b5b0917b3f71a) == "3.2469628020730493e-65"
#guard fmtReal (Float.ofBits 0x8a4d65c24d0cd46a) == "-4.7799580221816089e-259"
#guard fmtReal (Float.ofBits 0xe86dd67f7d0489b2) == "-1.0890685480960122e+195"
#guard fmtReal (Float.ofBits 0xab22fc24e2d71379) == "-6.7811076787874896e-101"
#guard fmtReal (Float.ofBits 0x372108d44d1d0a79) == "3.8192646272472767e-43"
#guard fmtReal (Float.ofBits 0x5921f4769d00881d) == "2.3182064222045743e+121"
#guard fmtReal (Float.ofBits 0x4dabd9ea003248f3) == "1.4665382610105298e+66"
#guard fmtReal (Float.ofBits 0x176f9838c21940c8) == "8.4532928297897979e-196"
#guard fmtReal (Float.ofBits 0xf4ac182142b18715) == "-1.0298735893004578e+254"
#guard fmtReal (Float.ofBits 0xa056d9b838df726b) == "-6.8170628268153401e-153"
#guard fmtReal (Float.ofBits 0x1a7ff57003b09c12) == "4.8136252177816629e-181"
#guard fmtReal (Float.ofBits 0x5b7f550297c17042) == "5.5599029246095859e+132"
#guard fmtReal (Float.ofBits 0xf92384930724347c) == "-3.3787685014362632e+275"
#guard fmtReal (Float.ofBits 0x18ca53919db18c95) == "2.9543699862882136e-189"
#guard fmtReal (Float.ofBits 0x09a2cf6aa7ad66c7) == "2.9868106243589736e-262"
#guard fmtReal (Float.ofBits 0x8e63381bd90dc0f7) == "-2.3058348320238194e-239"
#guard fmtReal (Float.ofBits 0xb225913a6c163466) == "-3.999877664542244e-67"
#guard fmtReal (Float.ofBits 0x5b775df707cf2670) == "4.1465032409873287e+132"
#guard fmtReal (Float.ofBits 0x0ea0980de2512460) == "3.1853967004223159e-238"
#guard fmtReal (Float.ofBits 0x2797732410777762) == "5.8119287052778119e-118"
#guard fmtReal (Float.ofBits 0xa127251204623ba4) == "-5.6564727994668184e-149"
#guard fmtReal (Float.ofBits 0x7982320fe5b7c692) == "2.0159108977249168e+277"
#guard fmtReal (Float.ofBits 0x8a1e500d26bea417) == "-6.1609599557452096e-260"
#guard fmtReal (Float.ofBits 0x581c3dbd4f78e217) == "2.7818968782905012e+116"
#guard fmtReal (Float.ofBits 0x47d738139c977f16) == "1.2345364119757084e+38"
#guard fmtReal (Float.ofBits 0xfd76a997a9795c49) == "-2.3158104061449314e+296"
#guard fmtReal (Float.ofBits 0x2052d770db589d02) == "5.6210727083423447e-153"
#guard fmtReal (Float.ofBits 0x8da8f37ccedd53d3) == "-7.3084218595830179e-243"
#guard fmtReal (Float.ofBits 0xeeeb472cea0626de) == "-2.0193878973845434e+226"
#guard fmtReal (Float.ofBits 0x323aab2adc3ab511) == "9.8919419519200045e-67"
#guard fmtReal (Float.ofBits 0x0d50441317ad1f73) == "1.4888881159976465e-244"
#guard fmtReal (Float.ofBits 0xd8ae8211589b1861) == "-1.5386616910276496e+119"
#guard fmtReal (Float.ofBits 0x08d48d492204a0c8) == "3.9836003329541121e-266"
#guard fmtReal (Float.ofBits 0xa41807cbe10233e8) == "-8.2654012136688226e-135"
#guard fmtReal (Float.ofBits 0x973161e889ab8050) == "-5.8134500534790951e-197"
#guard fmtReal (Float.ofBits 0x3187a23c205af2b2) == "4.2803894783198568e-70"
#guard fmtReal (Float.ofBits 0xbfd6e0d52e6f40df) == "-0.35747270140292459"
#guard fmtReal (Float.ofBits 0xf966019efe28d230) == "-6.0952805365386983e+276"
#guard fmtReal (Float.ofBits 0xb6cda472694ccdb7) == "-1.0384452162652731e-44"
#guard fmtReal (Float.ofBits 0xcab68320b3a4708b) == "-8.4228206298007617e+51"
#guard fmtReal (Float.ofBits 0xc984cb0a8e421dac) == "-1.483847327782713e+46"
#guard fmtReal (Float.ofBits 0x3cdb3e86cb53377e) == "1.5123593653439226e-15"
#guard fmtReal (Float.ofBits 0x4ccf1e1d00b357c9) == "1.0000820713824282e+62"
#guard fmtReal (Float.ofBits 0x10cdb896087a2387) == "9.8016069565734061e-228"
#guard fmtReal (Float.ofBits 0xa4076b026412a848) == "-4.0273730006407947e-135"
#guard fmtReal (Float.ofBits 0x5d48220e71e4171e) == "2.2991107332194529e+141"
#guard fmtReal (Float.ofBits 0xf4a83385dcc4b774) == "-8.87164925276e+253"
#guard fmtReal (Float.ofBits 0xafd967ae39196207) == "-3.428154390501465e-78"
#guard fmtReal (Float.ofBits 0x63093cca93080ebd) == "1.1905656066182473e+169"
#guard fmtReal (Float.ofBits 0x09240b6a63cc163b) == "1.2432860009064968e-264"
#guard fmtReal (Float.ofBits 0x179b0bc8765e00e3) == "5.789036725217422e-195"
#guard fmtReal (Float.ofBits 0x4aecfe8be15805ce) == "8.6784509818581056e+52"
#guard fmtReal (Float.ofBits 0x881a324d798c437f) == "-1.2396728116446414e-269"
#guard fmtReal (Float.ofBits 0x3229693955957db9) == "4.7127376429753034e-67"
#guard fmtReal (Float.ofBits 0xa0ebca3d1b5b289d) == "-4.2448333006221646e-150"
#guard fmtReal (Float.ofBits 0x6cafdcab0894641e) == "3.4324146166450235e+215"
#guard fmtReal (Float.ofBits 0x5a5e684d53112c46) == "2.0583437328777535e+127"
#guard fmtReal (Float.ofBits 0x6432bacdb1532e65) == "4.6324244977645626e+174"
#guard fmtReal (Float.ofBits 0xf4f7b9d8bd69e0b4) == "-2.7831729655178887e+255"
#guard fmtReal (Float.ofBits 0x62c7523e4c6036d6) == "6.8760602053514627e+167"
#guard fmtReal (Float.ofBits 0xc358308b39cea4a5) == "-27235095877948052.0"
#guard fmtReal (Float.ofBits 0x78ebeea21e744220) == "3.0221123635982964e+274"
#guard fmtReal (Float.ofBits 0x1d9d95cd8dfcd75f) == "5.0171425250530378e-166"
#guard fmtReal (Float.ofBits 0x034322e9e886dacc) == "5.9925829129800906e-293"
#guard fmtReal (Float.ofBits 0x0c3f05b47770df74) == "1.0832217964616921e-249"
#guard fmtReal (Float.ofBits 0x2b701cc803782b8a) == "1.8416300863500865e-99"
#guard fmtReal (Float.ofBits 0xeb11d52b408dd0f1) == "-5.7252428794706875e+207"
#guard fmtReal (Float.ofBits 0x6f307e98ce019643) == "3.9074767074014207e+227"
#guard fmtReal (Float.ofBits 0x64f403ba7eeb04e1) == "2.0276061227607374e+178"
#guard fmtReal (Float.ofBits 0x301db10ccc7d085b) == "6.4105418901015547e-77"
#guard fmtReal (Float.ofBits 0xa879afff09c2d88d) == "-1.0430934991475392e-113"
#guard fmtReal (Float.ofBits 0x7906ef16bb99e3e5) == "9.9253251356377267e+274"
#guard fmtReal (Float.ofBits 0x00c1b991149ab4d7) == "5.0482105456719461e-305"
#guard fmtReal (Float.ofBits 0xfc8fc093d5a34b34) == "-9.9019424993751397e+291"
#guard fmtReal (Float.ofBits 0x95f8a85b36279d71) == "-7.8645607242385761e-203"
#guard fmtReal (Float.ofBits 0xd07344d6fb88c1b7) == "-3.56989889681571e+79"
#guard fmtReal (Float.ofBits 0xbac4e9718b5a9526) == "-1.351399139581707e-25"
#guard fmtReal (Float.ofBits 0x06fc124dfcead4a2) == "5.0674518438332173e-275"
#guard fmtReal (Float.ofBits 0x1685284663af7227) == "3.4550443789369553e-200"
#guard fmtReal (Float.ofBits 0x47150253583fcaf7) == "2.7271350524432258e+34"
#guard fmtReal (Float.ofBits 0xed8cc39a91ee318f) == "-5.076884738075989e+219"
#guard fmtReal (Float.ofBits 0x3267c4200596cea3) == "7.0522731837132566e-66"
#guard fmtReal (Float.ofBits 0x211658e559bc6ca2) == "2.7307770184802452e-149"
#guard fmtReal (Float.ofBits 0xf128c77f4cac2681) == "-1.2605944666011627e+237"
#guard fmtReal (Float.ofBits 0x3d0a609b94004963) == "1.1713907148207019e-14"
#guard fmtReal (Float.ofBits 0x5e8c5bc30745f17e) == "2.832893870950059e+147"
#guard fmtReal (Float.ofBits 0xfc9a07ef9a7b149e) == "-1.6235537098441178e+292"
#guard fmtReal (Float.ofBits 0xd141c17bd148a1ef) == "-2.6948149751618859e+83"
#guard fmtReal (Float.ofBits 0x5a55209d863a3020) == "1.4301589785550672e+127"
#guard fmtReal (Float.ofBits 0xce98b0a3e7b20caa) == "-4.2601031038484167e+70"
#guard fmtReal (Float.ofBits 0x093652766c682cb0) == "2.7691038563655063e-264"
#guard fmtReal (Float.ofBits 0xd27e5d4a0dff1508) == "-2.4161483627023711e+89"
#guard fmtReal (Float.ofBits 0xfd86d87647740e14) == "-4.6690385055397291e+296"
#guard fmtReal (Float.ofBits 0x45a08f16547dcb70) == "2.562371e+27"
#guard fmtReal (Float.ofBits 0x469281364926414f) == "9.383015161321e+31"
#guard fmtReal (Float.ofBits 0x483315ea36d2a200) == "6.4944948688123805e+39"
#guard fmtReal (Float.ofBits 0x4023851eb851eb85) == "9.76"
#guard fmtReal (Float.ofBits 0x437358a7451fd800) == "87128000000000000.0"
#guard fmtReal (Float.ofBits 0x40f232a1717efe0d) == "74538.090209"
#guard fmtReal (Float.ofBits 0x40bc153ef73c0c20) == "7189.24596"
#guard fmtReal (Float.ofBits 0x43050d6209b90400) == "740711154000000.0"
#guard fmtReal (Float.ofBits 0x401a5949be65f21b) == "6.5871953725550396"
#guard fmtReal (Float.ofBits 0x0000000000000000) == "0.0"
#guard fmtReal (Float.ofBits 0x42fe853664eaab80) == "536919873071800.0"
#guard fmtReal (Float.ofBits 0x4586ae550574fe70) == "8.774281013122e+26"
#guard fmtReal (Float.ofBits 0x42beb1b15348b000) == "33748533070000.0"
#guard fmtReal (Float.ofBits 0x419312d000000000) == "80000000.0"
#guard fmtReal (Float.ofBits 0x46215a4d69af7a51) == "6.87413e+29"
#guard fmtReal (Float.ofBits 0x48e66ef74b1e749b) == "1.5633840481719701e+43"
#guard fmtReal (Float.ofBits 0x4256679b22048ccd) == "384910002194.2"
#guard fmtReal (Float.ofBits 0x42f9c5b7ccaef700) == "453391726342000.0"
#guard fmtReal (Float.ofBits 0x3f7409e115a6b87b) == "0.004892234074232"
#guard fmtReal (Float.ofBits 0x45ae8095c169c4bb) == "4.72e+27"
#guard fmtReal (Float.ofBits 0x44b0386f7884248d) == "7.659891370927e+22"
#guard fmtReal (Float.ofBits 0x3fc501824447108d) == "0.16410854658"
#guard fmtReal (Float.ofBits 0x42f50b1ba81c1900) == "370199245210000.0"
#guard fmtReal (Float.ofBits 0x4336afde3b4ae900) == "6385818500000000.0"
#guard fmtReal (Float.ofBits 0x3dd07e1fe91b0b70) == "6.0e-11"
#guard fmtReal (Float.ofBits 0x3d0436c5aa1842fb) == "8.976798691e-15"
#guard fmtReal (Float.ofBits 0x420e5f424f000000) == "16305900000.0"
#guard fmtReal (Float.ofBits 0x3d6e1a46fd18d61e) == "8.555686492e-13"
#guard fmtReal (Float.ofBits 0x466938e85b39e408) == "1.5986529e+31"
#guard fmtReal (Float.ofBits 0x3d66aec9b451130b) == "6.446829634204e-13"
#guard fmtReal (Float.ofBits 0x3f7b089a02752546) == "0.0066"
#guard fmtReal (Float.ofBits 0x461418078901d89d) == "3.98e+29"
#guard fmtReal (Float.ofBits 0x4374facb288f5400) == "94484000000000000.0"
#guard fmtReal (Float.ofBits 0x424e449a94000000) == "260000000000.0"
#guard fmtReal (Float.ofBits 0x427076face280000) == "1131450000000.0"
#guard fmtReal (Float.ofBits 0x46c6c69a7d9b8eb1) == "9.23896e+32"
#guard fmtReal (Float.ofBits 0x42c760c0f3c36000) == "51408643000000.0"
#guard fmtReal (Float.ofBits 0x3e111f57d21aef69) == "9.966568199391e-10"
#guard fmtReal (Float.ofBits 0x3e77b437f7b9de53) == "8.8304203e-08"
#guard fmtReal (Float.ofBits 0x3f7cac083126e979) == "0.007"
#guard fmtReal (Float.ofBits 0x479a18e68e4a8251) == "8.67230481067e+36"
#guard fmtReal (Float.ofBits 0x43394505390755a1) == "7112763151701409.0"
#guard fmtReal (Float.ofBits 0x46b5c70a14ca180d) == "4.41700126e+32"
#guard fmtReal (Float.ofBits 0x3f79cbee807bbb62) == "0.006298"
#guard fmtReal (Float.ofBits 0x3eaf8f5d877f4cad) == "9.4056191723493e-07"
#guard fmtReal (Float.ofBits 0x3d61719fe290e7db) == "4.957839195711e-13"
#guard fmtReal (Float.ofBits 0x4072d95a858793de) == "301.5846"
#guard fmtReal (Float.ofBits 0x3ea03b622a648d05) == "4.83750302736e-07"
#guard fmtReal (Float.ofBits 0x3e4af85dd73e0a3f) == "1.2558969621e-08"
#guard fmtReal (Float.ofBits 0x45d500ac8a0ecb42) == "2.6e+28"
#guard fmtReal (Float.ofBits 0x3f682a9930be0ded) == "0.00295"
#guard fmtReal (Float.ofBits 0x483cc240a7d77477) == "9.7861122162e+39"
#guard fmtReal (Float.ofBits 0x447cd55c2ff01555) == "8.5101288e+21"
#guard fmtReal (Float.ofBits 0x4541f646f0548ed7) == "4.3429499355886619e+25"
#guard fmtReal (Float.ofBits 0x3f7af3a14cec41dd) == "0.00658"
#guard fmtReal (Float.ofBits 0x3d9ef9a80e3fbd97) == "7.04294975e-12"
#guard fmtReal (Float.ofBits 0x4217fd81e182f0a4) == "25759348832.735001"
#guard fmtReal (Float.ofBits 0x3ee35cb6db2d0c0d) == "9.23259981323e-06"
#guard fmtReal (Float.ofBits 0x4640354f2ab6ffb3) == "2.56829802520727e+30"
#guard fmtReal (Float.ofBits 0x43e14cb786f67ee3) == "9.9725838973103698e+18"
#guard fmtReal (Float.ofBits 0x408a25e04102ff8f) == "836.734499"
#guard fmtReal (Float.ofBits 0x44de85b5a3e0cba2) == "5.7655e+23"
#guard fmtReal (Float.ofBits 0x408d83999999999a) == "944.45"
#guard fmtReal (Float.ofBits 0x3cfd56cfe30210bd) == "6.514591e-15"
#guard fmtReal (Float.ofBits 0x448e31ab9cc41b6a) == "1.7823406365e+22"
#guard fmtReal (Float.ofBits 0x3dbf329800b0644c) == "2.83740809e-11"
#guard fmtReal (Float.ofBits 0x44b4b59dc318a159) == "9.77975582917e+22"
#guard fmtReal (Float.ofBits 0x3c469f8b4abe30db) == "2.452814338e-18"
#guard fmtReal (Float.ofBits 0x42bb48eb57e00000) == "30000000000000.0"
#guard fmtReal (Float.ofBits 0x45d200feeb791bc2) == "2.228773600633e+28"
#guard fmtReal (Float.ofBits 0x42ff4971939b92b0) == "550404777163051.0"
#guard fmtReal (Float.ofBits 0x3d96edcdb854cf6d) == "5.21343288e-12"
#guard fmtReal (Float.ofBits 0x3b9d79dd8db8a6cb) == "1.5604484e-21"
#guard fmtReal (Float.ofBits 0x42436b4fdba04ccd) == "166809548608.6"
#guard fmtReal (Float.ofBits 0x3f49596d599fae87) == "0.0007736"
#guard fmtReal (Float.ofBits 0x46bba9d1536fef62) == "5.61079402e+32"
#guard fmtReal (Float.ofBits 0x3fcd304a4aa6ed3f) == "0.2280362"
#guard fmtReal (Float.ofBits 0x4382dfb0cb5e8800) == "1.7e+17"
#guard fmtReal (Float.ofBits 0x3f0f827c46a27bc0) == "6.01e-05"
#guard fmtReal (Float.ofBits 0x0000000000000000) == "0.0"
#guard fmtReal (Float.ofBits 0x3e98531d0fd32671) == "3.624657124e-07"
#guard fmtReal (Float.ofBits 0x441f176e0d108a72) == "1.4338434189e+20"
#guard fmtReal (Float.ofBits 0x4195cc5d11a0ded3) == "91428676.4071"
#guard fmtReal (Float.ofBits 0x41fa4e7c21400000) == "7061619220.0"
#guard fmtReal (Float.ofBits 0x41b76e4b4b59c4d2) == "393104203.35065949"
#guard fmtReal (Float.ofBits 0x44dc0dc0409365fb) == "5.2991968971131318e+23"
#guard fmtReal (Float.ofBits 0x3eda607006babd47) == "6.2886975730613506e-06"
#guard fmtReal (Float.ofBits 0x414afe2781b23e97) == "3537999.0132520902"
#guard fmtReal (Float.ofBits 0x42fabfaf1c369c00) == "470569263000000.0"
#guard fmtReal (Float.ofBits 0x3cedfb057a3c07cc) == "3.32850994874e-15"
#guard fmtReal (Float.ofBits 0x3c25f1719e9537cf) == "5.9477e-19"
#guard fmtReal (Float.ofBits 0x477cb0cc31dae61f) == "2.3835231056603009e+36"
#guard fmtReal (Float.ofBits 0x4571351712fb9040) == "3.328392e+26"
#guard fmtReal (Float.ofBits 0x3c91962aabd259f5) == "6.101573625e-17"
#guard fmtReal (Float.ofBits 0x3c7a04ca000c2520) == "2.2567631165047e-17"
#guard fmtReal (Float.ofBits 0x3f03a67bd0e6bae4) == "3.7480023923e-05"
#guard fmtReal (Float.ofBits 0x422c829fe0400000) == "61225300000.0"
#guard fmtReal (Float.ofBits 0x3ee20f7ca6117620) == "8.6119154635812462e-06"
#guard fmtReal (Float.ofBits 0x3dd0c47e4f1fc318) == "6.1e-11"
#guard fmtReal (Float.ofBits 0x3dbf8dbe750b0845) == "2.8697911508274021e-11"
#guard fmtReal (Float.ofBits 0x46211f8be18817a8) == "6.7832095188940116e+29"
#guard fmtReal (Float.ofBits 0x3df49da7e361ce4c) == "3.0e-10"
#guard fmtReal (Float.ofBits 0x3eed83c90d9e80f3) == "1.4073746957e-05"
#guard fmtReal (Float.ofBits 0x428db5ed01e25414) == "4083400326218.5098"
#guard fmtReal (Float.ofBits 0x3b96aad80c11872c) == "1.2e-21"
#guard fmtReal (Float.ofBits 0x44f52d02c7e14af6) == "1.6e+24"
#guard fmtReal (Float.ofBits 0x40ac200000000000) == "3600.0"
#guard fmtReal (Float.ofBits 0x3f826e978d4fdf3b) == "0.009"
#guard fmtReal (Float.ofBits 0x3b84f6a9db0887cf) == "5.549e-22"
#guard fmtReal (Float.ofBits 0x4017e24adb458b7a) == "5.97098868"
#guard fmtReal (Float.ofBits 0x3aebfc9a4cead477) == "7.2344e-25"
#guard fmtReal (Float.ofBits 0x3db19f0f07e5b5db) == "1.60265e-11"
#guard fmtReal (Float.ofBits 0x4161a8961c8c7c4d) == "9258160.892149115"
#guard fmtReal (Float.ofBits 0x3c4bad0baf1281ae) == "3.000633545e-18"
#guard fmtReal (Float.ofBits 0x3eb04700be65826a) == "9.7020596853e-07"
#guard fmtReal (Float.ofBits 0x3cbc675bb8cce9ed) == "3.9418112267e-16"
#guard fmtReal (Float.ofBits 0x3e8b1121ad9cebb4) == "2.0166427e-07"
#guard fmtReal (Float.ofBits 0x3e18305f867c045b) == "1.407982641881e-09"
#guard fmtReal (Float.ofBits 0x3eacf53f386a559e) == "8.6301553e-07"
#guard fmtReal (Float.ofBits 0x44a97c3e673b31e4) == "6.0175527482359766e+22"
#guard fmtReal (Float.ofBits 0x408f3995574539b0) == "999.19792036135004"
#guard fmtReal (Float.ofBits 0x3fe5fe36e197a2dd) == "0.68728202878"
#guard fmtReal (Float.ofBits 0x41e14e094cc398e3) == "2322614886.1124129"
#guard fmtReal (Float.ofBits 0x4731ecc359022473) == "9.30711723e+34"
#guard fmtReal (Float.ofBits 0x421bbd4ec1740000) == "29785043037.0"
#guard fmtReal (Float.ofBits 0x000b3803e8a4959a) == "1.5601675037581294e-308"
#guard fmtReal (Float.ofBits 0x0007663382002e82) == "1.028988666557795e-308"
#guard fmtReal (Float.ofBits 0x00029dc3d6e27677) == "3.6383705751162814e-309"
#guard fmtReal (Float.ofBits 0x0006172f5a91730a) == "8.469974926832424e-309"
#guard fmtReal (Float.ofBits 0x00000d00eff14260) == "7.0639908860953272e-311"
#guard fmtReal (Float.ofBits 0x00046c0fae53a170) == "6.1497067919416974e-309"
#guard fmtReal (Float.ofBits 0x0009fb885f831d63) == "1.3882443900868893e-308"
#guard fmtReal (Float.ofBits 0x00009fcb8b9dea9e) == "8.6805639111609619e-310"
#guard fmtReal (Float.ofBits 0x0005585eb58cea17) == "7.4334087444673334e-309"
#guard fmtReal (Float.ofBits 0x000dfe9c0ab65018) == "1.9461842844858022e-308"
#guard fmtReal (Float.ofBits 0x000547e04818a74f) == "7.3438090094683705e-309"
#guard fmtReal (Float.ofBits 0x000dcba3312836a1) == "1.9184946800812416e-308"
#guard fmtReal (Float.ofBits 0x000a7911053c53fc) == "1.4564382205149854e-308"
#guard fmtReal (Float.ofBits 0x0008b68cd9b68e66) == "1.2117038411909888e-308"
#guard fmtReal (Float.ofBits 0x000841f574c248eb) == "1.1483677960041575e-308"
#guard fmtReal (Float.ofBits 0x00085d2546c9bcb6) == "1.1631365056544563e-308"
#guard fmtReal (Float.ofBits 0x000973f11b4ef7b7) == "1.3145872288430845e-308"
#guard fmtReal (Float.ofBits 0x4407e8cef0c922d6) == "5.5131340512998113e+19"
#guard fmtReal (Float.ofBits 0xc3b62dc9143a4b87) == "-1.5981545315009513e+18"
#guard fmtReal (Float.ofBits 0x415d6ffcc0000000) == "7716851.0"
#guard fmtReal (Float.ofBits 0xc42237be9597afd5) == "-1.6802910286157778e+20"
#guard fmtReal (Float.ofBits 0xc3e1eb483791ca97) == "-1.0329640973425228e+19"
#guard fmtReal (Float.ofBits 0xc3a84360cb938e94) == "-8.7417375391005338e+17"
#guard fmtReal (Float.ofBits 0xc427d7efb2340f95) == "-2.1991748243478875e+20"
#guard fmtReal (Float.ofBits 0xc344b061fc4c7d19) == "-11646868850801202.0"
#guard fmtReal (Float.ofBits 0xc1950e9a30000000) == "-88319628.0"
#guard fmtReal (Float.ofBits 0xc1dba88ecc800000) == "-1856125746.0"
#guard fmtReal (Float.ofBits 0x41826f2170000000) == "38659118.0"
#guard fmtReal (Float.ofBits 0x4134fa0000000000) == "1374720.0"
#guard fmtReal (Float.ofBits 0xc2939030b086d400) == "-5377503273397.0"
#guard fmtReal (Float.ofBits 0x41d58e2b1f000000) == "1446554748.0"
#guard fmtReal (Float.ofBits 0x4199d25ce4000000) == "108304185.0"
#guard fmtReal (Float.ofBits 0xc1c1883c9e800000) == "-588282173.0"
#guard fmtReal (Float.ofBits 0x41f380c83eb00000) == "5235311595.0"
#guard fmtReal (Float.ofBits 0xc1b9f142fd000000) == "-435241725.0"
#guard fmtReal (Float.ofBits 0xc1cc854a05800000) == "-956994571.0"
#guard fmtReal (Float.ofBits 0x42a0727f00d81e00) == "9041971538959.0"
#guard fmtReal (Float.ofBits 0x4373de3f9cff7003) == "89478229692710960.0"
#guard fmtReal (Float.ofBits 0x4164eda880000000) == "10972484.0"
#guard fmtReal (Float.ofBits 0xc16982d120000000) == "-13375113.0"
#guard fmtReal (Float.ofBits 0xc1a1b0e45c000000) == "-148402734.0"
#guard fmtReal (Float.ofBits 0x42681f80bc996000) == "828861965515.0"
#guard fmtReal (Float.ofBits 0x416312cfffffffff) == "9999999.9999999981"
#guard fmtReal (Float.ofBits 0x4197d78400000000) == "100000000.0"
#guard fmtReal (Float.ofBits 0x412e847fffffffcc) == "999999.99999999395"
#guard fmtReal (Float.ofBits 0x3c9cd2b297d8896b) == "9.9999999999999e-17"
#guard fmtReal (Float.ofBits 0x3f1a36e2eb1c42e3) == "9.9999999999999002e-05"
#guard fmtReal (Float.ofBits 0x3f847ae147ae147b) == "0.01"
#guard fmtReal (Float.ofBits 0x430c6bf52633fff0) == "999999999999998.0"
#guard fmtReal (Float.ofBits 0x3bc79ca10c924223) == "1.0e-20"

/-! ### Text to numbers: atoF, atoi64, affinity, casts, arithmetic -/
#guard (atoF "").value.toBits == 0x0000000000000000
#guard (atoi64 "").value == 0
#guard numStr "" == "text:"
#guard realStr "" == "text:"
#guard cnStr "" == "integer:0"
#guard nvStr "" == "integer:0"
#guard fmtReal (castToReal (.text "")) == "0.0"
#guard (atoF "0").value.toBits == 0x0000000000000000
#guard (atoi64 "0").value == 0
#guard numStr "0" == "integer:0"
#guard realStr "0" == "real:0.0"
#guard cnStr "0" == "integer:0"
#guard nvStr "0" == "integer:0"
#guard fmtReal (castToReal (.text "0")) == "0.0"
#guard (atoF "1").value.toBits == 0x3ff0000000000000
#guard (atoi64 "1").value == 1
#guard numStr "1" == "integer:1"
#guard realStr "1" == "real:1.0"
#guard cnStr "1" == "integer:1"
#guard nvStr "1" == "integer:1"
#guard fmtReal (castToReal (.text "1")) == "1.0"
#guard (atoF "-1").value.toBits == 0xbff0000000000000
#guard (atoi64 "-1").value == (-1)
#guard numStr "-1" == "integer:-1"
#guard realStr "-1" == "real:-1.0"
#guard cnStr "-1" == "integer:-1"
#guard nvStr "-1" == "integer:-1"
#guard fmtReal (castToReal (.text "-1")) == "-1.0"
#guard (atoF "+1").value.toBits == 0x3ff0000000000000
#guard (atoi64 "+1").value == 1
#guard numStr "+1" == "integer:1"
#guard realStr "+1" == "real:1.0"
#guard cnStr "+1" == "integer:1"
#guard nvStr "+1" == "integer:1"
#guard fmtReal (castToReal (.text "+1")) == "1.0"
#guard (atoF " 12 ").value.toBits == 0x4028000000000000
#guard (atoi64 " 12 ").value == 12
#guard numStr " 12 " == "integer:12"
#guard realStr " 12 " == "real:12.0"
#guard cnStr " 12 " == "integer:12"
#guard nvStr " 12 " == "integer:12"
#guard fmtReal (castToReal (.text " 12 ")) == "12.0"
#guard (atoF "12abc").value.toBits == 0x4028000000000000
#guard (atoi64 "12abc").value == 12
#guard numStr "12abc" == "text:12abc"
#guard realStr "12abc" == "text:12abc"
#guard cnStr "12abc" == "integer:12"
#guard nvStr "12abc" == "integer:12"
#guard fmtReal (castToReal (.text "12abc")) == "12.0"
#guard (atoF "abc").value.toBits == 0x0000000000000000
#guard (atoi64 "abc").value == 0
#guard numStr "abc" == "text:abc"
#guard realStr "abc" == "text:abc"
#guard cnStr "abc" == "integer:0"
#guard nvStr "abc" == "integer:0"
#guard fmtReal (castToReal (.text "abc")) == "0.0"
#guard (atoF "1e2").value.toBits == 0x4059000000000000
#guard (atoi64 "1e2").value == 1
#guard numStr "1e2" == "integer:100"
#guard realStr "1e2" == "real:100.0"
#guard cnStr "1e2" == "integer:100"
#guard nvStr "1e2" == "real:100.0"
#guard fmtReal (castToReal (.text "1e2")) == "100.0"
#guard (atoF "3.0").value.toBits == 0x4008000000000000
#guard (atoi64 "3.0").value == 3
#guard numStr "3.0" == "integer:3"
#guard realStr "3.0" == "real:3.0"
#guard cnStr "3.0" == "integer:3"
#guard nvStr "3.0" == "real:3.0"
#guard fmtReal (castToReal (.text "3.0")) == "3.0"
#guard (atoF "3.5").value.toBits == 0x400c000000000000
#guard (atoi64 "3.5").value == 3
#guard numStr "3.5" == "real:3.5"
#guard realStr "3.5" == "real:3.5"
#guard cnStr "3.5" == "real:3.5"
#guard nvStr "3.5" == "real:3.5"
#guard fmtReal (castToReal (.text "3.5")) == "3.5"
#guard (atoF " 7 ").value.toBits == 0x401c000000000000
#guard (atoi64 " 7 ").value == 7
#guard numStr " 7 " == "integer:7"
#guard realStr " 7 " == "real:7.0"
#guard cnStr " 7 " == "integer:7"
#guard nvStr " 7 " == "integer:7"
#guard fmtReal (castToReal (.text " 7 ")) == "7.0"
#guard (atoF "0x10").value.toBits == 0x0000000000000000
#guard (atoi64 "0x10").value == 0
#guard numStr "0x10" == "text:0x10"
#guard realStr "0x10" == "text:0x10"
#guard cnStr "0x10" == "integer:0"
#guard nvStr "0x10" == "integer:0"
#guard fmtReal (castToReal (.text "0x10")) == "0.0"
#guard (atoF "9223372036854775807").value.toBits == 0x43e0000000000000
#guard (atoi64 "9223372036854775807").value == 9223372036854775807
#guard numStr "9223372036854775807" == "integer:9223372036854775807"
#guard realStr "9223372036854775807" == "real:9.2233720368547758e+18"
#guard cnStr "9223372036854775807" == "integer:9223372036854775807"
#guard nvStr "9223372036854775807" == "integer:9223372036854775807"
#guard fmtReal (castToReal (.text "9223372036854775807")) == "9.2233720368547758e+18"
#guard (atoF "9223372036854775808").value.toBits == 0x43e0000000000000
#guard (atoi64 "9223372036854775808").value == 9223372036854775807
#guard numStr "9223372036854775808" == "real:9.2233720368547758e+18"
#guard realStr "9223372036854775808" == "real:9.2233720368547758e+18"
#guard cnStr "9223372036854775808" == "real:9.2233720368547758e+18"
#guard nvStr "9223372036854775808" == "real:9.2233720368547758e+18"
#guard fmtReal (castToReal (.text "9223372036854775808")) == "9.2233720368547758e+18"
#guard (atoF "-9223372036854775808").value.toBits == 0xc3e0000000000000
#guard (atoi64 "-9223372036854775808").value == (-9223372036854775808)
#guard numStr "-9223372036854775808" == "integer:-9223372036854775808"
#guard realStr "-9223372036854775808" == "real:-9.2233720368547758e+18"
#guard cnStr "-9223372036854775808" == "integer:-9223372036854775808"
#guard nvStr "-9223372036854775808" == "integer:-9223372036854775808"
#guard fmtReal (castToReal (.text "-9223372036854775808")) == "-9.2233720368547758e+18"
#guard (atoF "-9223372036854775809").value.toBits == 0xc3e0000000000000
#guard (atoi64 "-9223372036854775809").value == (-9223372036854775808)
#guard numStr "-9223372036854775809" == "real:-9.2233720368547758e+18"
#guard realStr "-9223372036854775809" == "real:-9.2233720368547758e+18"
#guard cnStr "-9223372036854775809" == "real:-9.2233720368547758e+18"
#guard nvStr "-9223372036854775809" == "real:-9.2233720368547758e+18"
#guard fmtReal (castToReal (.text "-9223372036854775809")) == "-9.2233720368547758e+18"
#guard (atoF "1.5x").value.toBits == 0x3ff8000000000000
#guard (atoi64 "1.5x").value == 1
#guard numStr "1.5x" == "text:1.5x"
#guard realStr "1.5x" == "text:1.5x"
#guard cnStr "1.5x" == "real:1.5"
#guard nvStr "1.5x" == "real:1.5"
#guard fmtReal (castToReal (.text "1.5x")) == "1.5"
#guard (atoF ".5").value.toBits == 0x3fe0000000000000
#guard (atoi64 ".5").value == 0
#guard numStr ".5" == "real:0.5"
#guard realStr ".5" == "real:0.5"
#guard cnStr ".5" == "real:0.5"
#guard nvStr ".5" == "real:0.5"
#guard fmtReal (castToReal (.text ".5")) == "0.5"
#guard (atoF "5.").value.toBits == 0x4014000000000000
#guard (atoi64 "5.").value == 5
#guard numStr "5." == "integer:5"
#guard realStr "5." == "real:5.0"
#guard cnStr "5." == "integer:5"
#guard nvStr "5." == "real:5.0"
#guard fmtReal (castToReal (.text "5.")) == "5.0"
#guard (atoF ".").value.toBits == 0x0000000000000000
#guard (atoi64 ".").value == 0
#guard numStr "." == "text:."
#guard realStr "." == "text:."
#guard cnStr "." == "integer:0"
#guard nvStr "." == "integer:0"
#guard fmtReal (castToReal (.text ".")) == "0.0"
#guard (atoF "-").value.toBits == 0x0000000000000000
#guard (atoi64 "-").value == 0
#guard numStr "-" == "text:-"
#guard realStr "-" == "text:-"
#guard cnStr "-" == "integer:0"
#guard nvStr "-" == "integer:0"
#guard fmtReal (castToReal (.text "-")) == "0.0"
#guard (atoF "+").value.toBits == 0x0000000000000000
#guard (atoi64 "+").value == 0
#guard numStr "+" == "text:+"
#guard realStr "+" == "text:+"
#guard cnStr "+" == "integer:0"
#guard nvStr "+" == "integer:0"
#guard fmtReal (castToReal (.text "+")) == "0.0"
#guard (atoF "e5").value.toBits == 0x0000000000000000
#guard (atoi64 "e5").value == 0
#guard numStr "e5" == "text:e5"
#guard realStr "e5" == "text:e5"
#guard cnStr "e5" == "integer:0"
#guard nvStr "e5" == "integer:0"
#guard fmtReal (castToReal (.text "e5")) == "0.0"
#guard (atoF "1e").value.toBits == 0x3ff0000000000000
#guard (atoi64 "1e").value == 1
#guard numStr "1e" == "text:1e"
#guard realStr "1e" == "text:1e"
#guard cnStr "1e" == "integer:1"
#guard nvStr "1e" == "integer:1"
#guard fmtReal (castToReal (.text "1e")) == "1.0"
#guard (atoF "1e+").value.toBits == 0x3ff0000000000000
#guard (atoi64 "1e+").value == 1
#guard numStr "1e+" == "text:1e+"
#guard realStr "1e+" == "text:1e+"
#guard cnStr "1e+" == "integer:1"
#guard nvStr "1e+" == "integer:1"
#guard fmtReal (castToReal (.text "1e+")) == "1.0"
#guard (atoF "1e-5").value.toBits == 0x3ee4f8b588e368f1
#guard (atoi64 "1e-5").value == 1
#guard numStr "1e-5" == "real:1.0e-05"
#guard realStr "1e-5" == "real:1.0e-05"
#guard cnStr "1e-5" == "real:1.0e-05"
#guard nvStr "1e-5" == "real:1.0e-05"
#guard fmtReal (castToReal (.text "1e-5")) == "1.0e-05"
#guard (atoF "1E5").value.toBits == 0x40f86a0000000000
#guard (atoi64 "1E5").value == 1
#guard numStr "1E5" == "integer:100000"
#guard realStr "1E5" == "real:100000.0"
#guard cnStr "1E5" == "integer:100000"
#guard nvStr "1E5" == "real:100000.0"
#guard fmtReal (castToReal (.text "1E5")) == "100000.0"
#guard (atoF "  ").value.toBits == 0x0000000000000000
#guard (atoi64 "  ").value == 0
#guard numStr "  " == "text:  "
#guard realStr "  " == "text:  "
#guard cnStr "  " == "integer:0"
#guard nvStr "  " == "integer:0"
#guard fmtReal (castToReal (.text "  ")) == "0.0"
#guard (atoF "\t12\n").value.toBits == 0x4028000000000000
#guard (atoi64 "\t12\n").value == 12
#guard numStr "\t12\n" == "integer:12"
#guard realStr "\t12\n" == "real:12.0"
#guard cnStr "\t12\n" == "integer:12"
#guard nvStr "\t12\n" == "integer:12"
#guard fmtReal (castToReal (.text "\t12\n")) == "12.0"
#guard (atoF "12 3").value.toBits == 0x4028000000000000
#guard (atoi64 "12 3").value == 12
#guard numStr "12 3" == "text:12 3"
#guard realStr "12 3" == "text:12 3"
#guard cnStr "12 3" == "integer:12"
#guard nvStr "12 3" == "integer:12"
#guard fmtReal (castToReal (.text "12 3")) == "12.0"
#guard (atoF "0.0").value.toBits == 0x0000000000000000
#guard (atoi64 "0.0").value == 0
#guard numStr "0.0" == "integer:0"
#guard realStr "0.0" == "real:0.0"
#guard cnStr "0.0" == "integer:0"
#guard nvStr "0.0" == "real:0.0"
#guard fmtReal (castToReal (.text "0.0")) == "0.0"
#guard (atoF "-0.0").value.toBits == 0x8000000000000000
#guard (atoi64 "-0.0").value == 0
#guard numStr "-0.0" == "integer:0"
#guard realStr "-0.0" == "real:0.0"
#guard cnStr "-0.0" == "integer:0"
#guard nvStr "-0.0" == "real:0.0"
#guard fmtReal (castToReal (.text "-0.0")) == "0.0"
#guard (atoF "-0").value.toBits == 0x8000000000000000
#guard (atoi64 "-0").value == 0
#guard numStr "-0" == "integer:0"
#guard realStr "-0" == "real:0.0"
#guard cnStr "-0" == "integer:0"
#guard nvStr "-0" == "integer:0"
#guard fmtReal (castToReal (.text "-0")) == "0.0"
#guard (atoF "1e308").value.toBits == 0x7fe1ccf385ebc8a0
#guard (atoi64 "1e308").value == 1
#guard numStr "1e308" == "real:1.0e+308"
#guard realStr "1e308" == "real:1.0e+308"
#guard cnStr "1e308" == "real:1.0e+308"
#guard nvStr "1e308" == "real:1.0e+308"
#guard fmtReal (castToReal (.text "1e308")) == "1.0e+308"
#guard (atoF "1e309").value.toBits == 0x7ff0000000000000
#guard (atoi64 "1e309").value == 1
#guard numStr "1e309" == "real:Inf"
#guard realStr "1e309" == "real:Inf"
#guard cnStr "1e309" == "real:Inf"
#guard nvStr "1e309" == "real:Inf"
#guard fmtReal (castToReal (.text "1e309")) == "Inf"
#guard (atoF "-1e309").value.toBits == 0xfff0000000000000
#guard (atoi64 "-1e309").value == (-1)
#guard numStr "-1e309" == "real:-Inf"
#guard realStr "-1e309" == "real:-Inf"
#guard cnStr "-1e309" == "real:-Inf"
#guard nvStr "-1e309" == "real:-Inf"
#guard fmtReal (castToReal (.text "-1e309")) == "-Inf"
#guard (atoF "1e-400").value.toBits == 0x0000000000000000
#guard (atoi64 "1e-400").value == 1
#guard numStr "1e-400" == "integer:0"
#guard realStr "1e-400" == "real:0.0"
#guard cnStr "1e-400" == "integer:0"
#guard nvStr "1e-400" == "real:0.0"
#guard fmtReal (castToReal (.text "1e-400")) == "0.0"
#guard (atoF "0000123").value.toBits == 0x405ec00000000000
#guard (atoi64 "0000123").value == 123
#guard numStr "0000123" == "integer:123"
#guard realStr "0000123" == "real:123.0"
#guard cnStr "0000123" == "integer:123"
#guard nvStr "0000123" == "integer:123"
#guard fmtReal (castToReal (.text "0000123")) == "123.0"
#guard (atoF "00").value.toBits == 0x0000000000000000
#guard (atoi64 "00").value == 0
#guard numStr "00" == "integer:0"
#guard realStr "00" == "real:0.0"
#guard cnStr "00" == "integer:0"
#guard nvStr "00" == "integer:0"
#guard fmtReal (castToReal (.text "00")) == "0.0"
#guard (atoF "9223372036854775807.0").value.toBits == 0x43e0000000000000
#guard (atoi64 "9223372036854775807.0").value == 9223372036854775807
#guard numStr "9223372036854775807.0" == "real:9.2233720368547758e+18"
#guard realStr "9223372036854775807.0" == "real:9.2233720368547758e+18"
#guard cnStr "9223372036854775807.0" == "real:9.2233720368547758e+18"
#guard nvStr "9223372036854775807.0" == "real:9.2233720368547758e+18"
#guard fmtReal (castToReal (.text "9223372036854775807.0")) == "9.2233720368547758e+18"
#guard (atoF "-9223372036854775808.0").value.toBits == 0xc3e0000000000000
#guard (atoi64 "-9223372036854775808.0").value == (-9223372036854775808)
#guard numStr "-9223372036854775808.0" == "real:-9.2233720368547758e+18"
#guard realStr "-9223372036854775808.0" == "real:-9.2233720368547758e+18"
#guard cnStr "-9223372036854775808.0" == "real:-9.2233720368547758e+18"
#guard nvStr "-9223372036854775808.0" == "real:-9.2233720368547758e+18"
#guard fmtReal (castToReal (.text "-9223372036854775808.0")) == "-9.2233720368547758e+18"
#guard (atoF "9223372036854775808.0").value.toBits == 0x43e0000000000000
#guard (atoi64 "9223372036854775808.0").value == 9223372036854775807
#guard numStr "9223372036854775808.0" == "real:9.2233720368547758e+18"
#guard realStr "9223372036854775808.0" == "real:9.2233720368547758e+18"
#guard cnStr "9223372036854775808.0" == "real:9.2233720368547758e+18"
#guard nvStr "9223372036854775808.0" == "real:9.2233720368547758e+18"
#guard fmtReal (castToReal (.text "9223372036854775808.0")) == "9.2233720368547758e+18"
#guard (atoF "1.0e0").value.toBits == 0x3ff0000000000000
#guard (atoi64 "1.0e0").value == 1
#guard numStr "1.0e0" == "integer:1"
#guard realStr "1.0e0" == "real:1.0"
#guard cnStr "1.0e0" == "integer:1"
#guard nvStr "1.0e0" == "real:1.0"
#guard fmtReal (castToReal (.text "1.0e0")) == "1.0"
#guard (atoF "4503599627370496").value.toBits == 0x4330000000000000
#guard (atoi64 "4503599627370496").value == 4503599627370496
#guard numStr "4503599627370496" == "integer:4503599627370496"
#guard realStr "4503599627370496" == "real:4503599627370496.0"
#guard cnStr "4503599627370496" == "integer:4503599627370496"
#guard nvStr "4503599627370496" == "integer:4503599627370496"
#guard fmtReal (castToReal (.text "4503599627370496")) == "4503599627370496.0"
#guard (atoF "2251799813685248").value.toBits == 0x4320000000000000
#guard (atoi64 "2251799813685248").value == 2251799813685248
#guard numStr "2251799813685248" == "integer:2251799813685248"
#guard realStr "2251799813685248" == "real:2251799813685248.0"
#guard cnStr "2251799813685248" == "integer:2251799813685248"
#guard nvStr "2251799813685248" == "integer:2251799813685248"
#guard fmtReal (castToReal (.text "2251799813685248")) == "2251799813685248.0"
#guard (atoF "2251799813685247.0").value.toBits == 0x431ffffffffffffc
#guard (atoi64 "2251799813685247.0").value == 2251799813685247
#guard numStr "2251799813685247.0" == "integer:2251799813685247"
#guard realStr "2251799813685247.0" == "real:2251799813685247.0"
#guard cnStr "2251799813685247.0" == "integer:2251799813685247"
#guard nvStr "2251799813685247.0" == "real:2251799813685247.0"
#guard fmtReal (castToReal (.text "2251799813685247.0")) == "2251799813685247.0"
#guard (atoF "1e18").value.toBits == 0x43abc16d674ec800
#guard (atoi64 "1e18").value == 1
#guard numStr "1e18" == "integer:1000000000000000000"
#guard realStr "1e18" == "real:1.0e+18"
#guard cnStr "1e18" == "real:1.0e+18"
#guard nvStr "1e18" == "real:1.0e+18"
#guard fmtReal (castToReal (.text "1e18")) == "1.0e+18"
#guard (atoF "1e19").value.toBits == 0x43e158e460913d00
#guard (atoi64 "1e19").value == 1
#guard numStr "1e19" == "real:1.0e+19"
#guard realStr "1e19" == "real:1.0e+19"
#guard cnStr "1e19" == "real:1.0e+19"
#guard nvStr "1e19" == "real:1.0e+19"
#guard fmtReal (castToReal (.text "1e19")) == "1.0e+19"
#guard (atoF "123456789012345678901234567890").value.toBits == 0x45f8ee90ff6c373e
#guard (atoi64 "123456789012345678901234567890").value == 9223372036854775807
#guard numStr "123456789012345678901234567890" == "real:1.2345678901234568e+29"
#guard realStr "123456789012345678901234567890" == "real:1.2345678901234568e+29"
#guard cnStr "123456789012345678901234567890" == "real:1.2345678901234568e+29"
#guard nvStr "123456789012345678901234567890" == "real:1.2345678901234568e+29"
#guard fmtReal (castToReal (.text "123456789012345678901234567890")) == "1.2345678901234568e+29"
#guard (atoF "0.000000000000000000000001").value.toBits == 0x3af357c299a88ea7
#guard (atoi64 "0.000000000000000000000001").value == 0
#guard numStr "0.000000000000000000000001" == "real:1.0e-24"
#guard realStr "0.000000000000000000000001" == "real:1.0e-24"
#guard cnStr "0.000000000000000000000001" == "real:1.0e-24"
#guard nvStr "0.000000000000000000000001" == "real:1.0e-24"
#guard fmtReal (castToReal (.text "0.000000000000000000000001")) == "1.0e-24"
#guard (atoF "1.7976931348623157e308").value.toBits == 0x7fefffffffffffff
#guard (atoi64 "1.7976931348623157e308").value == 1
#guard numStr "1.7976931348623157e308" == "real:1.7976931348623157e+308"
#guard realStr "1.7976931348623157e308" == "real:1.7976931348623157e+308"
#guard cnStr "1.7976931348623157e308" == "real:1.7976931348623157e+308"
#guard nvStr "1.7976931348623157e308" == "real:1.7976931348623157e+308"
#guard fmtReal (castToReal (.text "1.7976931348623157e308")) == "1.7976931348623157e+308"
#guard (atoF "5e-324").value.toBits == 0x0000000000000001
#guard (atoi64 "5e-324").value == 5
#guard numStr "5e-324" == "real:4.9406564584124654e-324"
#guard realStr "5e-324" == "real:4.9406564584124654e-324"
#guard cnStr "5e-324" == "real:4.9406564584124654e-324"
#guard nvStr "5e-324" == "real:4.9406564584124654e-324"
#guard fmtReal (castToReal (.text "5e-324")) == "4.9406564584124654e-324"
#guard (atoF "2.2250738585072011e-308").value.toBits == 0x000fffffffffffff
#guard (atoi64 "2.2250738585072011e-308").value == 2
#guard numStr "2.2250738585072011e-308" == "real:2.2250738585072009e-308"
#guard realStr "2.2250738585072011e-308" == "real:2.2250738585072009e-308"
#guard cnStr "2.2250738585072011e-308" == "real:2.2250738585072009e-308"
#guard nvStr "2.2250738585072011e-308" == "real:2.2250738585072009e-308"
#guard fmtReal (castToReal (.text "2.2250738585072011e-308")) == "2.2250738585072009e-308"
#guard (atoF "Inf").value.toBits == 0x0000000000000000
#guard (atoi64 "Inf").value == 0
#guard numStr "Inf" == "text:Inf"
#guard realStr "Inf" == "text:Inf"
#guard cnStr "Inf" == "integer:0"
#guard nvStr "Inf" == "integer:0"
#guard fmtReal (castToReal (.text "Inf")) == "0.0"
#guard (atoF "inf").value.toBits == 0x0000000000000000
#guard (atoi64 "inf").value == 0
#guard numStr "inf" == "text:inf"
#guard realStr "inf" == "text:inf"
#guard cnStr "inf" == "integer:0"
#guard nvStr "inf" == "integer:0"
#guard fmtReal (castToReal (.text "inf")) == "0.0"
#guard (atoF "-Inf").value.toBits == 0x0000000000000000
#guard (atoi64 "-Inf").value == 0
#guard numStr "-Inf" == "text:-Inf"
#guard realStr "-Inf" == "text:-Inf"
#guard cnStr "-Inf" == "integer:0"
#guard nvStr "-Inf" == "integer:0"
#guard fmtReal (castToReal (.text "-Inf")) == "0.0"
#guard (atoF "nan").value.toBits == 0x0000000000000000
#guard (atoi64 "nan").value == 0
#guard numStr "nan" == "text:nan"
#guard realStr "nan" == "text:nan"
#guard cnStr "nan" == "integer:0"
#guard nvStr "nan" == "integer:0"
#guard fmtReal (castToReal (.text "nan")) == "0.0"
#guard (atoF "NaN").value.toBits == 0x0000000000000000
#guard (atoi64 "NaN").value == 0
#guard numStr "NaN" == "text:NaN"
#guard realStr "NaN" == "text:NaN"
#guard cnStr "NaN" == "integer:0"
#guard nvStr "NaN" == "integer:0"
#guard fmtReal (castToReal (.text "NaN")) == "0.0"
#guard (atoF "1_000").value.toBits == 0x3ff0000000000000
#guard (atoi64 "1_000").value == 1
#guard numStr "1_000" == "text:1_000"
#guard realStr "1_000" == "text:1_000"
#guard cnStr "1_000" == "integer:1"
#guard nvStr "1_000" == "integer:1"
#guard fmtReal (castToReal (.text "1_000")) == "1.0"
#guard (atoF "١٢٣").value.toBits == 0x0000000000000000
#guard (atoi64 "١٢٣").value == 0
#guard numStr "١٢٣" == "text:١٢٣"
#guard realStr "١٢٣" == "text:١٢٣"
#guard cnStr "١٢٣" == "integer:0"
#guard nvStr "١٢٣" == "integer:0"
#guard fmtReal (castToReal (.text "١٢٣")) == "0.0"
#guard (atoF "12é").value.toBits == 0x4028000000000000
#guard (atoi64 "12é").value == 12
#guard numStr "12é" == "text:12é"
#guard realStr "12é" == "text:12é"
#guard cnStr "12é" == "integer:12"
#guard nvStr "12é" == "integer:12"
#guard fmtReal (castToReal (.text "12é")) == "12.0"
#guard (atoF "٣").value.toBits == 0x0000000000000000
#guard (atoi64 "٣").value == 0
#guard numStr "٣" == "text:٣"
#guard realStr "٣" == "text:٣"
#guard cnStr "٣" == "integer:0"
#guard nvStr "٣" == "integer:0"
#guard fmtReal (castToReal (.text "٣")) == "0.0"
#guard (atoF "+-5").value.toBits == 0x0000000000000000
#guard (atoi64 "+-5").value == 0
#guard numStr "+-5" == "text:+-5"
#guard realStr "+-5" == "text:+-5"
#guard cnStr "+-5" == "integer:0"
#guard nvStr "+-5" == "integer:0"
#guard fmtReal (castToReal (.text "+-5")) == "0.0"
#guard (atoF "--5").value.toBits == 0x0000000000000000
#guard (atoi64 "--5").value == 0
#guard numStr "--5" == "text:--5"
#guard realStr "--5" == "text:--5"
#guard cnStr "--5" == "integer:0"
#guard nvStr "--5" == "integer:0"
#guard fmtReal (castToReal (.text "--5")) == "0.0"
#guard (atoF "1e5.5").value.toBits == 0x40f86a0000000000
#guard (atoi64 "1e5.5").value == 1
#guard numStr "1e5.5" == "text:1e5.5"
#guard realStr "1e5.5" == "text:1e5.5"
#guard cnStr "1e5.5" == "integer:100000"
#guard nvStr "1e5.5" == "real:100000.0"
#guard fmtReal (castToReal (.text "1e5.5")) == "100000.0"
#guard (atoF "1.2.3").value.toBits == 0x3ff3333333333333
#guard (atoi64 "1.2.3").value == 1
#guard numStr "1.2.3" == "text:1.2.3"
#guard realStr "1.2.3" == "text:1.2.3"
#guard cnStr "1.2.3" == "real:1.2"
#guard nvStr "1.2.3" == "real:1.2"
#guard fmtReal (castToReal (.text "1.2.3")) == "1.2"
#guard (atoF "0x").value.toBits == 0x0000000000000000
#guard (atoi64 "0x").value == 0
#guard numStr "0x" == "text:0x"
#guard realStr "0x" == "text:0x"
#guard cnStr "0x" == "integer:0"
#guard nvStr "0x" == "integer:0"
#guard fmtReal (castToReal (.text "0x")) == "0.0"
#guard (atoF "0xg").value.toBits == 0x0000000000000000
#guard (atoi64 "0xg").value == 0
#guard numStr "0xg" == "text:0xg"
#guard realStr "0xg" == "text:0xg"
#guard cnStr "0xg" == "integer:0"
#guard nvStr "0xg" == "integer:0"
#guard fmtReal (castToReal (.text "0xg")) == "0.0"
#guard (atoF "１２").value.toBits == 0x0000000000000000
#guard (atoi64 "１２").value == 0
#guard numStr "１２" == "text:１２"
#guard realStr "１２" == "text:１２"
#guard cnStr "１２" == "integer:0"
#guard nvStr "１２" == "integer:0"
#guard fmtReal (castToReal (.text "１２")) == "0.0"
#guard (atoF " +7").value.toBits == 0x401c000000000000
#guard (atoi64 " +7").value == 7
#guard numStr " +7" == "integer:7"
#guard realStr " +7" == "real:7.0"
#guard cnStr " +7" == "integer:7"
#guard nvStr " +7" == "integer:7"
#guard fmtReal (castToReal (.text " +7")) == "7.0"
#guard (atoF "+ 7").value.toBits == 0x0000000000000000
#guard (atoi64 "+ 7").value == 0
#guard numStr "+ 7" == "text:+ 7"
#guard realStr "+ 7" == "text:+ 7"
#guard cnStr "+ 7" == "integer:0"
#guard nvStr "+ 7" == "integer:0"
#guard fmtReal (castToReal (.text "+ 7")) == "0.0"
#guard (atoF "1e+5").value.toBits == 0x40f86a0000000000
#guard (atoi64 "1e+5").value == 1
#guard numStr "1e+5" == "integer:100000"
#guard realStr "1e+5" == "real:100000.0"
#guard cnStr "1e+5" == "integer:100000"
#guard nvStr "1e+5" == "real:100000.0"
#guard fmtReal (castToReal (.text "1e+5")) == "100000.0"
#guard (atoF "1e-0").value.toBits == 0x3ff0000000000000
#guard (atoi64 "1e-0").value == 1
#guard numStr "1e-0" == "integer:1"
#guard realStr "1e-0" == "real:1.0"
#guard cnStr "1e-0" == "integer:1"
#guard nvStr "1e-0" == "real:1.0"
#guard fmtReal (castToReal (.text "1e-0")) == "1.0"
#guard (atoF "123e").value.toBits == 0x405ec00000000000
#guard (atoi64 "123e").value == 123
#guard numStr "123e" == "text:123e"
#guard realStr "123e" == "text:123e"
#guard cnStr "123e" == "integer:123"
#guard nvStr "123e" == "integer:123"
#guard fmtReal (castToReal (.text "123e")) == "123.0"
#guard (atoF "0e0").value.toBits == 0x0000000000000000
#guard (atoi64 "0e0").value == 0
#guard numStr "0e0" == "integer:0"
#guard realStr "0e0" == "real:0.0"
#guard cnStr "0e0" == "integer:0"
#guard nvStr "0e0" == "real:0.0"
#guard fmtReal (castToReal (.text "0e0")) == "0.0"
#guard (atoF "-.5e1").value.toBits == 0xc014000000000000
#guard (atoi64 "-.5e1").value == 0
#guard numStr "-.5e1" == "integer:-5"
#guard realStr "-.5e1" == "real:-5.0"
#guard cnStr "-.5e1" == "integer:-5"
#guard nvStr "-.5e1" == "real:-5.0"
#guard fmtReal (castToReal (.text "-.5e1")) == "-5.0"
#guard (atoF ".e1").value.toBits == 0x0000000000000000
#guard (atoi64 ".e1").value == 0
#guard numStr ".e1" == "text:.e1"
#guard realStr ".e1" == "text:.e1"
#guard cnStr ".e1" == "integer:0"
#guard nvStr ".e1" == "integer:0"
#guard fmtReal (castToReal (.text ".e1")) == "0.0"
#guard (atoF "1.e1").value.toBits == 0x4024000000000000
#guard (atoi64 "1.e1").value == 1
#guard numStr "1.e1" == "integer:10"
#guard realStr "1.e1" == "real:10.0"
#guard cnStr "1.e1" == "integer:10"
#guard nvStr "1.e1" == "real:10.0"
#guard fmtReal (castToReal (.text "1.e1")) == "10.0"
#guard (atoF "3.0e").value.toBits == 0x4008000000000000
#guard (atoi64 "3.0e").value == 3
#guard numStr "3.0e" == "text:3.0e"
#guard realStr "3.0e" == "text:3.0e"
#guard cnStr "3.0e" == "integer:3"
#guard nvStr "3.0e" == "real:3.0"
#guard fmtReal (castToReal (.text "3.0e")) == "3.0"
#guard (atoF "2e2 x").value.toBits == 0x4069000000000000
#guard (atoi64 "2e2 x").value == 2
#guard numStr "2e2 x" == "text:2e2 x"
#guard realStr "2e2 x" == "text:2e2 x"
#guard cnStr "2e2 x" == "integer:200"
#guard nvStr "2e2 x" == "real:200.0"
#guard fmtReal (castToReal (.text "2e2 x")) == "200.0"
#guard (atoF "e5").value.toBits == 0x0000000000000000
#guard (atoi64 "e5").value == 0
#guard numStr "e5" == "text:e5"
#guard realStr "e5" == "text:e5"
#guard cnStr "e5" == "integer:0"
#guard nvStr "e5" == "integer:0"
#guard fmtReal (castToReal (.text "e5")) == "0.0"
#guard (atoF "-").value.toBits == 0x0000000000000000
#guard (atoi64 "-").value == 0
#guard numStr "-" == "text:-"
#guard realStr "-" == "text:-"
#guard cnStr "-" == "integer:0"
#guard nvStr "-" == "integer:0"
#guard fmtReal (castToReal (.text "-")) == "0.0"
#guard (atoF " 11692233720368547758071e10  ").value.toBits == 0x46970f11ca097fb4
#guard (atoi64 " 11692233720368547758071e10  ").value == 9223372036854775807
#guard numStr " 11692233720368547758071e10  " == "real:1.1692233720368548e+32"
#guard realStr " 11692233720368547758071e10  " == "real:1.1692233720368548e+32"
#guard cnStr " 11692233720368547758071e10  " == "real:1.1692233720368548e+32"
#guard nvStr " 11692233720368547758071e10  " == "real:1.1692233720368548e+32"
#guard fmtReal (castToReal (.text " 11692233720368547758071e10  ")) == "1.1692233720368548e+32"
#guard (atoF "").value.toBits == 0x0000000000000000
#guard (atoi64 "").value == 0
#guard numStr "" == "text:"
#guard realStr "" == "text:"
#guard cnStr "" == "integer:0"
#guard nvStr "" == "integer:0"
#guard fmtReal (castToReal (.text "")) == "0.0"
#guard (atoF "\t").value.toBits == 0x0000000000000000
#guard (atoi64 "\t").value == 0
#guard numStr "\t" == "text:\t"
#guard realStr "\t" == "text:\t"
#guard cnStr "\t" == "integer:0"
#guard nvStr "\t" == "integer:0"
#guard fmtReal (castToReal (.text "\t")) == "0.0"
#guard (atoF ".7").value.toBits == 0x3fe6666666666666
#guard (atoi64 ".7").value == 0
#guard numStr ".7" == "real:0.7"
#guard realStr ".7" == "real:0.7"
#guard cnStr ".7" == "real:0.7"
#guard nvStr ".7" == "real:0.7"
#guard fmtReal (castToReal (.text ".7")) == "0.7"
#guard (atoF "00e40.1.").value.toBits == 0x0000000000000000
#guard (atoi64 "00e40.1.").value == 0
#guard numStr "00e40.1." == "text:00e40.1."
#guard realStr "00e40.1." == "text:00e40.1."
#guard cnStr "00e40.1." == "integer:0"
#guard nvStr "00e40.1." == "real:0.0"
#guard fmtReal (castToReal (.text "00e40.1.")) == "0.0"
#guard (atoF "05110163415228482845z639760").value.toBits == 0x43d1babca3493901
#guard (atoi64 "05110163415228482845z639760").value == 5110163415228482845
#guard numStr "05110163415228482845z639760" == "text:05110163415228482845z639760"
#guard realStr "05110163415228482845z639760" == "text:05110163415228482845z639760"
#guard cnStr "05110163415228482845z639760" == "integer:5110163415228482845"
#guard nvStr "05110163415228482845z639760" == "integer:5110163415228482845"
#guard fmtReal (castToReal (.text "05110163415228482845z639760")) == "5.1101634152284826e+18"
#guard (atoF "-00").value.toBits == 0x8000000000000000
#guard (atoi64 "-00").value == 0
#guard numStr "-00" == "integer:0"
#guard realStr "-00" == "real:0.0"
#guard cnStr "-00" == "integer:0"
#guard nvStr "-00" == "integer:0"
#guard fmtReal (castToReal (.text "-00")) == "0.0"
#guard (atoF "992+.848224499790431e10").value.toBits == 0x408f000000000000
#guard (atoi64 "992+.848224499790431e10").value == 992
#guard numStr "992+.848224499790431e10" == "text:992+.848224499790431e10"
#guard realStr "992+.848224499790431e10" == "text:992+.848224499790431e10"
#guard cnStr "992+.848224499790431e10" == "integer:992"
#guard nvStr "992+.848224499790431e10" == "integer:992"
#guard fmtReal (castToReal (.text "992+.848224499790431e10")) == "992.0"
#guard (atoF "-").value.toBits == 0x0000000000000000
#guard (atoi64 "-").value == 0
#guard numStr "-" == "text:-"
#guard realStr "-" == "text:-"
#guard cnStr "-" == "integer:0"
#guard nvStr "-" == "integer:0"
#guard fmtReal (castToReal (.text "-")) == "0.0"
#guard (atoF "z0a98").value.toBits == 0x0000000000000000
#guard (atoi64 "z0a98").value == 0
#guard numStr "z0a98" == "text:z0a98"
#guard realStr "z0a98" == "text:z0a98"
#guard cnStr "z0a98" == "integer:0"
#guard nvStr "z0a98" == "integer:0"
#guard fmtReal (castToReal (.text "z0a98")) == "0.0"
#guard (atoF "54100887635340026175").value.toBits == 0x44077667b5530e1f
#guard (atoi64 "54100887635340026175").value == 9223372036854775807
#guard numStr "54100887635340026175" == "real:5.4100887635340026e+19"
#guard realStr "54100887635340026175" == "real:5.4100887635340026e+19"
#guard cnStr "54100887635340026175" == "real:5.4100887635340026e+19"
#guard nvStr "54100887635340026175" == "real:5.4100887635340026e+19"
#guard fmtReal (castToReal (.text "54100887635340026175")) == "5.4100887635340026e+19"
#guard (atoF "92233720368547758072448452992244974559428459").value.toBits == 0x49108b2a2c280291
#guard (atoi64 "92233720368547758072448452992244974559428459").value == 9223372036854775807
#guard numStr "92233720368547758072448452992244974559428459" == "real:9.2233720368547766e+43"
#guard realStr "92233720368547758072448452992244974559428459" == "real:9.2233720368547766e+43"
#guard cnStr "92233720368547758072448452992244974559428459" == "real:9.2233720368547766e+43"
#guard nvStr "92233720368547758072448452992244974559428459" == "real:9.2233720368547766e+43"
#guard fmtReal (castToReal (.text "92233720368547758072448452992244974559428459")) == "9.2233720368547766e+43"
#guard (atoF "e-\t3x").value.toBits == 0x0000000000000000
#guard (atoi64 "e-\t3x").value == 0
#guard numStr "e-\t3x" == "text:e-\t3x"
#guard realStr "e-\t3x" == "text:e-\t3x"
#guard cnStr "e-\t3x" == "integer:0"
#guard nvStr "e-\t3x" == "integer:0"
#guard fmtReal (castToReal (.text "e-\t3x")) == "0.0"
#guard (atoF "9183762997-0000").value.toBits == 0x42011b28d1a80000
#guard (atoi64 "9183762997-0000").value == 9183762997
#guard numStr "9183762997-0000" == "text:9183762997-0000"
#guard realStr "9183762997-0000" == "text:9183762997-0000"
#guard cnStr "9183762997-0000" == "integer:9183762997"
#guard nvStr "9183762997-0000" == "integer:9183762997"
#guard fmtReal (castToReal (.text "9183762997-0000")) == "9183762997.0"
#guard (atoF "+252232886589162504622866125").value.toBits == 0x456a148c85c794e6
#guard (atoi64 "+252232886589162504622866125").value == 9223372036854775807
#guard numStr "+252232886589162504622866125" == "real:2.5223288658916251e+26"
#guard realStr "+252232886589162504622866125" == "real:2.5223288658916251e+26"
#guard cnStr "+252232886589162504622866125" == "real:2.5223288658916251e+26"
#guard nvStr "+252232886589162504622866125" == "real:2.5223288658916251e+26"
#guard fmtReal (castToReal (.text "+252232886589162504622866125")) == "2.5223288658916251e+26"
#guard (atoF "0.").value.toBits == 0x0000000000000000
#guard (atoi64 "0.").value == 0
#guard numStr "0." == "integer:0"
#guard realStr "0." == "real:0.0"
#guard cnStr "0." == "integer:0"
#guard nvStr "0." == "real:0.0"
#guard fmtReal (castToReal (.text "0.")) == "0.0"
#guard (atoF "x +").value.toBits == 0x0000000000000000
#guard (atoi64 "x +").value == 0
#guard numStr "x +" == "text:x +"
#guard realStr "x +" == "text:x +"
#guard cnStr "x +" == "integer:0"
#guard nvStr "x +" == "integer:0"
#guard fmtReal (castToReal (.text "x +")) == "0.0"
#guard (atoF "E-3.184467440737095516150211").value.toBits == 0x0000000000000000
#guard (atoi64 "E-3.184467440737095516150211").value == 0
#guard numStr "E-3.184467440737095516150211" == "text:E-3.184467440737095516150211"
#guard realStr "E-3.184467440737095516150211" == "text:E-3.184467440737095516150211"
#guard cnStr "E-3.184467440737095516150211" == "integer:0"
#guard nvStr "E-3.184467440737095516150211" == "integer:0"
#guard fmtReal (castToReal (.text "E-3.184467440737095516150211")) == "0.0"
#guard (atoF "289122").value.toBits == 0x4111a58800000000
#guard (atoi64 "289122").value == 289122
#guard numStr "289122" == "integer:289122"
#guard realStr "289122" == "real:289122.0"
#guard cnStr "289122" == "integer:289122"
#guard nvStr "289122" == "integer:289122"
#guard fmtReal (castToReal (.text "289122")) == "289122.0"
#guard (atoF "837071223187701116971e3822016357032021436850").value.toBits == 0x7ff0000000000000
#guard (atoi64 "837071223187701116971e3822016357032021436850").value == 9223372036854775807
#guard numStr "837071223187701116971e3822016357032021436850" == "real:Inf"
#guard realStr "837071223187701116971e3822016357032021436850" == "real:Inf"
#guard cnStr "837071223187701116971e3822016357032021436850" == "real:Inf"
#guard nvStr "837071223187701116971e3822016357032021436850" == "real:Inf"
#guard fmtReal (castToReal (.text "837071223187701116971e3822016357032021436850")) == "Inf"
#guard (atoF "0784445").value.toBits == 0x4127f07a00000000
#guard (atoi64 "0784445").value == 784445
#guard numStr "0784445" == "integer:784445"
#guard realStr "0784445" == "real:784445.0"
#guard cnStr "0784445" == "integer:784445"
#guard nvStr "0784445" == "integer:784445"
#guard fmtReal (castToReal (.text "0784445")) == "784445.0"
#guard (atoF "93451521344099").value.toBits == 0x42d53f982ef098c0
#guard (atoi64 "93451521344099").value == 93451521344099
#guard numStr "93451521344099" == "integer:93451521344099"
#guard realStr "93451521344099" == "real:93451521344099.0"
#guard cnStr "93451521344099" == "integer:93451521344099"
#guard nvStr "93451521344099" == "integer:93451521344099"
#guard fmtReal (castToReal (.text "93451521344099")) == "93451521344099.0"
#guard (atoF "-0").value.toBits == 0x8000000000000000
#guard (atoi64 "-0").value == 0
#guard numStr "-0" == "integer:0"
#guard realStr "-0" == "real:0.0"
#guard cnStr "-0" == "integer:0"
#guard nvStr "-0" == "integer:0"
#guard fmtReal (castToReal (.text "-0")) == "0.0"
#guard (atoF "-760").value.toBits == 0xc087c00000000000
#guard (atoi64 "-760").value == (-760)
#guard numStr "-760" == "integer:-760"
#guard realStr "-760" == "real:-760.0"
#guard cnStr "-760" == "integer:-760"
#guard nvStr "-760" == "integer:-760"
#guard fmtReal (castToReal (.text "-760")) == "-760.0"
#guard (atoF "2  ").value.toBits == 0x4000000000000000
#guard (atoi64 "2  ").value == 2
#guard numStr "2  " == "integer:2"
#guard realStr "2  " == "real:2.0"
#guard cnStr "2  " == "integer:2"
#guard nvStr "2  " == "integer:2"
#guard fmtReal (castToReal (.text "2  ")) == "2.0"
#guard (atoF "6460").value.toBits == 0x40b93c0000000000
#guard (atoi64 "6460").value == 6460
#guard numStr "6460" == "integer:6460"
#guard realStr "6460" == "real:6460.0"
#guard cnStr "6460" == "integer:6460"
#guard nvStr "6460" == "integer:6460"
#guard fmtReal (castToReal (.text "6460")) == "6460.0"
#guard (atoF "8").value.toBits == 0x4020000000000000
#guard (atoi64 "8").value == 8
#guard numStr "8" == "integer:8"
#guard realStr "8" == "real:8.0"
#guard cnStr "8" == "integer:8"
#guard nvStr "8" == "integer:8"
#guard fmtReal (castToReal (.text "8")) == "8.0"
#guard (atoF "e+0019259264598300  ").value.toBits == 0x0000000000000000
#guard (atoi64 "e+0019259264598300  ").value == 0
#guard numStr "e+0019259264598300  " == "text:e+0019259264598300  "
#guard realStr "e+0019259264598300  " == "text:e+0019259264598300  "
#guard cnStr "e+0019259264598300  " == "integer:0"
#guard nvStr "e+0019259264598300  " == "integer:0"
#guard fmtReal (castToReal (.text "e+0019259264598300  ")) == "0.0"
#guard (atoF "0").value.toBits == 0x0000000000000000
#guard (atoi64 "0").value == 0
#guard numStr "0" == "integer:0"
#guard realStr "0" == "real:0.0"
#guard cnStr "0" == "integer:0"
#guard nvStr "0" == "integer:0"
#guard fmtReal (castToReal (.text "0")) == "0.0"
#guard (atoF ".7539967315397629247108676931820").value.toBits == 0x3fe820bdc0e82230
#guard (atoi64 ".7539967315397629247108676931820").value == 0
#guard numStr ".7539967315397629247108676931820" == "real:0.75399673153976288"
#guard realStr ".7539967315397629247108676931820" == "real:0.75399673153976288"
#guard cnStr ".7539967315397629247108676931820" == "real:0.75399673153976288"
#guard nvStr ".7539967315397629247108676931820" == "real:0.75399673153976288"
#guard fmtReal (castToReal (.text ".7539967315397629247108676931820")) == "0.75399673153976288"
#guard (atoF "\n154965112377052292088328321672").value.toBits == 0x45ff4b822f6eeda8
#guard (atoi64 "\n154965112377052292088328321672").value == 9223372036854775807
#guard numStr "\n154965112377052292088328321672" == "real:1.549651123770523e+29"
#guard realStr "\n154965112377052292088328321672" == "real:1.549651123770523e+29"
#guard cnStr "\n154965112377052292088328321672" == "real:1.549651123770523e+29"
#guard nvStr "\n154965112377052292088328321672" == "real:1.549651123770523e+29"
#guard fmtReal (castToReal (.text "\n154965112377052292088328321672")) == "1.549651123770523e+29"
#guard (atoF "2262375351963é  ").value.toBits == 0x42807600a234d800
#guard (atoi64 "2262375351963é  ").value == 2262375351963
#guard numStr "2262375351963é  " == "text:2262375351963é  "
#guard realStr "2262375351963é  " == "text:2262375351963é  "
#guard cnStr "2262375351963é  " == "integer:2262375351963"
#guard nvStr "2262375351963é  " == "integer:2262375351963"
#guard fmtReal (castToReal (.text "2262375351963é  ")) == "2262375351963.0"
#guard (atoF "000700079").value.toBits == 0x41255d5e00000000
#guard (atoi64 "000700079").value == 700079
#guard numStr "000700079" == "integer:700079"
#guard realStr "000700079" == "real:700079.0"
#guard cnStr "000700079" == "integer:700079"
#guard nvStr "000700079" == "integer:700079"
#guard fmtReal (castToReal (.text "000700079")) == "700079.0"
#guard (atoF "343\t").value.toBits == 0x4075700000000000
#guard (atoi64 "343\t").value == 343
#guard numStr "343\t" == "integer:343"
#guard realStr "343\t" == "real:343.0"
#guard cnStr "343\t" == "integer:343"
#guard nvStr "343\t" == "integer:343"
#guard fmtReal (castToReal (.text "343\t")) == "343.0"
#guard (atoF "152").value.toBits == 0x4063000000000000
#guard (atoi64 "152").value == 152
#guard numStr "152" == "integer:152"
#guard realStr "152" == "real:152.0"
#guard cnStr "152" == "integer:152"
#guard nvStr "152" == "integer:152"
#guard fmtReal (castToReal (.text "152")) == "152.0"
#guard (atoF "1e102+4").value.toBits == 0x551c931e8ab87173
#guard (atoi64 "1e102+4").value == 1
#guard numStr "1e102+4" == "text:1e102+4"
#guard realStr "1e102+4" == "text:1e102+4"
#guard cnStr "1e102+4" == "real:1.0e+102"
#guard nvStr "1e102+4" == "real:1.0e+102"
#guard fmtReal (castToReal (.text "1e102+4")) == "1.0e+102"
#guard (atoF "xE").value.toBits == 0x0000000000000000
#guard (atoi64 "xE").value == 0
#guard numStr "xE" == "text:xE"
#guard realStr "xE" == "text:xE"
#guard cnStr "xE" == "integer:0"
#guard nvStr "xE" == "integer:0"
#guard fmtReal (castToReal (.text "xE")) == "0.0"
#guard (atoF "00922337203685477580").value.toBits == 0x43a999999999999a
#guard (atoi64 "00922337203685477580").value == 922337203685477580
#guard numStr "00922337203685477580" == "integer:922337203685477580"
#guard realStr "00922337203685477580" == "real:9.2233720368547763e+17"
#guard cnStr "00922337203685477580" == "integer:922337203685477580"
#guard nvStr "00922337203685477580" == "integer:922337203685477580"
#guard fmtReal (castToReal (.text "00922337203685477580")) == "9.2233720368547763e+17"
#guard (atoF "4.é1e10z").value.toBits == 0x4010000000000000
#guard (atoi64 "4.é1e10z").value == 4
#guard numStr "4.é1e10z" == "text:4.é1e10z"
#guard realStr "4.é1e10z" == "text:4.é1e10z"
#guard cnStr "4.é1e10z" == "integer:4"
#guard nvStr "4.é1e10z" == "real:4.0"
#guard fmtReal (castToReal (.text "4.é1e10z")) == "4.0"
#guard (atoF "\t+25E  ").value.toBits == 0x4039000000000000
#guard (atoi64 "\t+25E  ").value == 25
#guard numStr "\t+25E  " == "text:\t+25E  "
#guard realStr "\t+25E  " == "text:\t+25E  "
#guard cnStr "\t+25E  " == "integer:25"
#guard nvStr "\t+25E  " == "integer:25"
#guard fmtReal (castToReal (.text "\t+25E  ")) == "25.0"
#guard (atoF "+1737").value.toBits == 0x409b240000000000
#guard (atoi64 "+1737").value == 1737
#guard numStr "+1737" == "integer:1737"
#guard realStr "+1737" == "real:1737.0"
#guard cnStr "+1737" == "integer:1737"
#guard nvStr "+1737" == "integer:1737"
#guard fmtReal (castToReal (.text "+1737")) == "1737.0"
#guard (atoF "632a").value.toBits == 0x4083c00000000000
#guard (atoi64 "632a").value == 632
#guard numStr "632a" == "text:632a"
#guard realStr "632a" == "text:632a"
#guard cnStr "632a" == "integer:632"
#guard nvStr "632a" == "integer:632"
#guard fmtReal (castToReal (.text "632a")) == "632.0"
#guard (atoF "000.25").value.toBits == 0x3fd0000000000000
#guard (atoi64 "000.25").value == 0
#guard numStr "000.25" == "real:0.25"
#guard realStr "000.25" == "real:0.25"
#guard cnStr "000.25" == "real:0.25"
#guard nvStr "000.25" == "real:0.25"
#guard fmtReal (castToReal (.text "000.25")) == "0.25"
#guard (atoF "000E8299.").value.toBits == 0x0000000000000000
#guard (atoi64 "000E8299.").value == 0
#guard numStr "000E8299." == "text:000E8299."
#guard realStr "000E8299." == "text:000E8299."
#guard cnStr "000E8299." == "integer:0"
#guard nvStr "000E8299." == "real:0.0"
#guard fmtReal (castToReal (.text "000E8299.")) == "0.0"
#guard (atoF "-59").value.toBits == 0xc04d800000000000
#guard (atoi64 "-59").value == (-59)
#guard numStr "-59" == "integer:-59"
#guard realStr "-59" == "real:-59.0"
#guard cnStr "-59" == "integer:-59"
#guard nvStr "-59" == "integer:-59"
#guard fmtReal (castToReal (.text "-59")) == "-59.0"
#guard (atoF "564").value.toBits == 0x4081a00000000000
#guard (atoi64 "564").value == 564
#guard numStr "564" == "integer:564"
#guard realStr "564" == "real:564.0"
#guard cnStr "564" == "integer:564"
#guard nvStr "564" == "integer:564"
#guard fmtReal (castToReal (.text "564")) == "564.0"
#guard (atoF " 9223372036854775807").value.toBits == 0x43e0000000000000
#guard (atoi64 " 9223372036854775807").value == 9223372036854775807
#guard numStr " 9223372036854775807" == "integer:9223372036854775807"
#guard realStr " 9223372036854775807" == "real:9.2233720368547758e+18"
#guard cnStr " 9223372036854775807" == "integer:9223372036854775807"
#guard nvStr " 9223372036854775807" == "integer:9223372036854775807"
#guard fmtReal (castToReal (.text " 9223372036854775807")) == "9.2233720368547758e+18"
#guard (atoF "973977064544589225999.é1").value.toBits == 0x444a6652d1ed02f9
#guard (atoi64 "973977064544589225999.é1").value == 9223372036854775807
#guard numStr "973977064544589225999.é1" == "text:973977064544589225999.é1"
#guard realStr "973977064544589225999.é1" == "text:973977064544589225999.é1"
#guard cnStr "973977064544589225999.é1" == "real:9.7397706454458919e+20"
#guard nvStr "973977064544589225999.é1" == "real:9.7397706454458919e+20"
#guard fmtReal (castToReal (.text "973977064544589225999.é1")) == "9.7397706454458919e+20"
#guard (atoF "51738818349825197382.72").value.toBits == 0x44067029a9523e58
#guard (atoi64 "51738818349825197382.72").value == 9223372036854775807
#guard numStr "51738818349825197382.72" == "real:5.1738818349825196e+19"
#guard realStr "51738818349825197382.72" == "real:5.1738818349825196e+19"
#guard cnStr "51738818349825197382.72" == "real:5.1738818349825196e+19"
#guard nvStr "51738818349825197382.72" == "real:5.1738818349825196e+19"
#guard fmtReal (castToReal (.text "51738818349825197382.72")) == "5.1738818349825196e+19"
#guard (atoF "61e10é18446744073709551615").value.toBits == 0x4261c0daaa800000
#guard (atoi64 "61e10é18446744073709551615").value == 61
#guard numStr "61e10é18446744073709551615" == "text:61e10é18446744073709551615"
#guard realStr "61e10é18446744073709551615" == "text:61e10é18446744073709551615"
#guard cnStr "61e10é18446744073709551615" == "integer:610000000000"
#guard nvStr "61e10é18446744073709551615" == "real:610000000000.0"
#guard fmtReal (castToReal (.text "61e10é18446744073709551615")) == "610000000000.0"
#guard (atoF "0.1e10").value.toBits == 0x41cdcd6500000000
#guard (atoi64 "0.1e10").value == 0
#guard numStr "0.1e10" == "integer:1000000000"
#guard realStr "0.1e10" == "real:1000000000.0"
#guard cnStr "0.1e10" == "integer:1000000000"
#guard nvStr "0.1e10" == "real:1000000000.0"
#guard fmtReal (castToReal (.text "0.1e10")) == "1000000000.0"
#guard (atoF "00e-e-").value.toBits == 0x0000000000000000
#guard (atoi64 "00e-e-").value == 0
#guard numStr "00e-e-" == "text:00e-e-"
#guard realStr "00e-e-" == "text:00e-e-"
#guard cnStr "00e-e-" == "integer:0"
#guard nvStr "00e-e-" == "integer:0"
#guard fmtReal (castToReal (.text "00e-e-")) == "0.0"
#guard (atoF "-").value.toBits == 0x0000000000000000
#guard (atoi64 "-").value == 0
#guard numStr "-" == "text:-"
#guard realStr "-" == "text:-"
#guard cnStr "-" == "integer:0"
#guard nvStr "-" == "integer:0"
#guard fmtReal (castToReal (.text "-")) == "0.0"
#guard (atoF "00138").value.toBits == 0x4061400000000000
#guard (atoi64 "00138").value == 138
#guard numStr "00138" == "integer:138"
#guard realStr "00138" == "real:138.0"
#guard cnStr "00138" == "integer:138"
#guard nvStr "00138" == "integer:138"
#guard fmtReal (castToReal (.text "00138")) == "138.0"
#guard (atoF ".6").value.toBits == 0x3fe3333333333333
#guard (atoi64 ".6").value == 0
#guard numStr ".6" == "real:0.6"
#guard realStr ".6" == "real:0.6"
#guard cnStr ".6" == "real:0.6"
#guard nvStr ".6" == "real:0.6"
#guard fmtReal (castToReal (.text ".6")) == "0.6"
#guard (atoF "440E").value.toBits == 0x407b800000000000
#guard (atoi64 "440E").value == 440
#guard numStr "440E" == "text:440E"
#guard realStr "440E" == "text:440E"
#guard cnStr "440E" == "integer:440"
#guard nvStr "440E" == "integer:440"
#guard fmtReal (castToReal (.text "440E")) == "440.0"
#guard (atoF ". ").value.toBits == 0x0000000000000000
#guard (atoi64 ". ").value == 0
#guard numStr ". " == "text:. "
#guard realStr ". " == "text:. "
#guard cnStr ". " == "integer:0"
#guard nvStr ". " == "integer:0"
#guard fmtReal (castToReal (.text ". ")) == "0.0"
#guard (atoF "9223372036854775809e+").value.toBits == 0x43e0000000000000
#guard (atoi64 "9223372036854775809e+").value == 9223372036854775807
#guard numStr "9223372036854775809e+" == "text:9223372036854775809e+"
#guard realStr "9223372036854775809e+" == "text:9223372036854775809e+"
#guard cnStr "9223372036854775809e+" == "real:9.2233720368547758e+18"
#guard nvStr "9223372036854775809e+" == "real:9.2233720368547758e+18"
#guard fmtReal (castToReal (.text "9223372036854775809e+")) == "9.2233720368547758e+18"
#guard (atoF "a1679473-000").value.toBits == 0x0000000000000000
#guard (atoi64 "a1679473-000").value == 0
#guard numStr "a1679473-000" == "text:a1679473-000"
#guard realStr "a1679473-000" == "text:a1679473-000"
#guard cnStr "a1679473-000" == "integer:0"
#guard nvStr "a1679473-000" == "integer:0"
#guard fmtReal (castToReal (.text "a1679473-000")) == "0.0"
#guard (atoF "0.186571640924034941227325063").value.toBits == 0x3fc7e1945c109cce
#guard (atoi64 "0.186571640924034941227325063").value == 0
#guard numStr "0.186571640924034941227325063" == "real:0.18657164092403494"
#guard realStr "0.186571640924034941227325063" == "real:0.18657164092403494"
#guard cnStr "0.186571640924034941227325063" == "real:0.18657164092403494"
#guard nvStr "0.186571640924034941227325063" == "real:0.18657164092403494"
#guard fmtReal (castToReal (.text "0.186571640924034941227325063")) == "0.18657164092403494"
#guard (atoF "2570.10").value.toBits == 0x40a4143333333333
#guard (atoi64 "2570.10").value == 2570
#guard numStr "2570.10" == "real:2570.1"
#guard realStr "2570.10" == "real:2570.1"
#guard cnStr "2570.10" == "real:2570.1"
#guard nvStr "2570.10" == "real:2570.1"
#guard fmtReal (castToReal (.text "2570.10")) == "2570.1"
#guard (atoF "60.1").value.toBits == 0x404e0ccccccccccd
#guard (atoi64 "60.1").value == 60
#guard numStr "60.1" == "real:60.1"
#guard realStr "60.1" == "real:60.1"
#guard cnStr "60.1" == "real:60.1"
#guard nvStr "60.1" == "real:60.1"
#guard fmtReal (castToReal (.text "60.1")) == "60.1"
#guard (atoF "  1e101e10-").value.toBits == 0x54e6dc186ef9f45c
#guard (atoi64 "  1e101e10-").value == 1
#guard numStr "  1e101e10-" == "text:  1e101e10-"
#guard realStr "  1e101e10-" == "text:  1e101e10-"
#guard cnStr "  1e101e10-" == "real:1.0e+101"
#guard nvStr "  1e101e10-" == "real:1.0e+101"
#guard fmtReal (castToReal (.text "  1e101e10-")) == "1.0e+101"
#guard (atoF "5E-").value.toBits == 0x4014000000000000
#guard (atoi64 "5E-").value == 5
#guard numStr "5E-" == "text:5E-"
#guard realStr "5E-" == "text:5E-"
#guard cnStr "5E-" == "integer:5"
#guard nvStr "5E-" == "integer:5"
#guard fmtReal (castToReal (.text "5E-")) == "5.0"
#guard (atoF "232-858").value.toBits == 0x406d000000000000
#guard (atoi64 "232-858").value == 232
#guard numStr "232-858" == "text:232-858"
#guard realStr "232-858" == "text:232-858"
#guard cnStr "232-858" == "integer:232"
#guard nvStr "232-858" == "integer:232"
#guard fmtReal (castToReal (.text "232-858")) == "232.0"
#guard (atoF "69797867534195414").value.toBits == 0x436eff194d8e935b
#guard (atoi64 "69797867534195414").value == 69797867534195414
#guard numStr "69797867534195414" == "integer:69797867534195414"
#guard realStr "69797867534195414" == "real:69797867534195416.0"
#guard cnStr "69797867534195414" == "integer:69797867534195414"
#guard nvStr "69797867534195414" == "integer:69797867534195414"
#guard fmtReal (castToReal (.text "69797867534195414")) == "69797867534195416.0"
#guard (atoF ".922337203685477580").value.toBits == 0x3fed83c94fb6d2ac
#guard (atoi64 ".922337203685477580").value == 0
#guard numStr ".922337203685477580" == "real:0.92233720368547756"
#guard realStr ".922337203685477580" == "real:0.92233720368547756"
#guard cnStr ".922337203685477580" == "real:0.92233720368547756"
#guard nvStr ".922337203685477580" == "real:0.92233720368547756"
#guard fmtReal (castToReal (.text ".922337203685477580")) == "0.92233720368547756"
#guard (atoF "E9223372036854775807az").value.toBits == 0x0000000000000000
#guard (atoi64 "E9223372036854775807az").value == 0
#guard numStr "E9223372036854775807az" == "text:E9223372036854775807az"
#guard realStr "E9223372036854775807az" == "text:E9223372036854775807az"
#guard cnStr "E9223372036854775807az" == "integer:0"
#guard nvStr "E9223372036854775807az" == "integer:0"
#guard fmtReal (castToReal (.text "E9223372036854775807az")) == "0.0"
#guard (atoF "e+e-4301306635794+0").value.toBits == 0x0000000000000000
#guard (atoi64 "e+e-4301306635794+0").value == 0
#guard numStr "e+e-4301306635794+0" == "text:e+e-4301306635794+0"
#guard realStr "e+e-4301306635794+0" == "text:e+e-4301306635794+0"
#guard cnStr "e+e-4301306635794+0" == "integer:0"
#guard nvStr "e+e-4301306635794+0" == "integer:0"
#guard fmtReal (castToReal (.text "e+e-4301306635794+0")) == "0.0"
#guard (atoF "  .").value.toBits == 0x0000000000000000
#guard (atoi64 "  .").value == 0
#guard numStr "  ." == "text:  ."
#guard realStr "  ." == "text:  ."
#guard cnStr "  ." == "integer:0"
#guard nvStr "  ." == "integer:0"
#guard fmtReal (castToReal (.text "  .")) == "0.0"
#guard (atoF "7").value.toBits == 0x401c000000000000
#guard (atoi64 "7").value == 7
#guard numStr "7" == "integer:7"
#guard realStr "7" == "real:7.0"
#guard cnStr "7" == "integer:7"
#guard nvStr "7" == "integer:7"
#guard fmtReal (castToReal (.text "7")) == "7.0"
#guard (atoF "-").value.toBits == 0x0000000000000000
#guard (atoi64 "-").value == 0
#guard numStr "-" == "text:-"
#guard realStr "-" == "text:-"
#guard cnStr "-" == "integer:0"
#guard nvStr "-" == "integer:0"
#guard fmtReal (castToReal (.text "-")) == "0.0"
#guard (atoF "516978900025591656193- ").value.toBits == 0x443c068602806d93
#guard (atoi64 "516978900025591656193- ").value == 9223372036854775807
#guard numStr "516978900025591656193- " == "text:516978900025591656193- "
#guard realStr "516978900025591656193- " == "text:516978900025591656193- "
#guard cnStr "516978900025591656193- " == "real:5.1697890002559166e+20"
#guard nvStr "516978900025591656193- " == "real:5.1697890002559166e+20"
#guard fmtReal (castToReal (.text "516978900025591656193- ")) == "5.1697890002559166e+20"
#guard (atoF "\n1\n506332").value.toBits == 0x3ff0000000000000
#guard (atoi64 "\n1\n506332").value == 1
#guard numStr "\n1\n506332" == "text:\n1\n506332"
#guard realStr "\n1\n506332" == "text:\n1\n506332"
#guard cnStr "\n1\n506332" == "integer:1"
#guard nvStr "\n1\n506332" == "integer:1"
#guard fmtReal (castToReal (.text "\n1\n506332")) == "1.0"
#guard (atoF "00070.1").value.toBits == 0x4051866666666666
#guard (atoi64 "00070.1").value == 70
#guard numStr "00070.1" == "real:70.1"
#guard realStr "00070.1" == "real:70.1"
#guard cnStr "00070.1" == "real:70.1"
#guard nvStr "00070.1" == "real:70.1"
#guard fmtReal (castToReal (.text "00070.1")) == "70.1"
#guard (atoF " 922337203685477580").value.toBits == 0x43a999999999999a
#guard (atoi64 " 922337203685477580").value == 922337203685477580
#guard numStr " 922337203685477580" == "integer:922337203685477580"
#guard realStr " 922337203685477580" == "real:9.2233720368547763e+17"
#guard cnStr " 922337203685477580" == "integer:922337203685477580"
#guard nvStr " 922337203685477580" == "integer:922337203685477580"
#guard fmtReal (castToReal (.text " 922337203685477580")) == "9.2233720368547763e+17"
#guard (atoF ". 25").value.toBits == 0x0000000000000000
#guard (atoi64 ". 25").value == 0
#guard numStr ". 25" == "text:. 25"
#guard realStr ". 25" == "text:. 25"
#guard cnStr ". 25" == "integer:0"
#guard nvStr ". 25" == "integer:0"
#guard fmtReal (castToReal (.text ". 25")) == "0.0"
#guard (atoF "5").value.toBits == 0x4014000000000000
#guard (atoi64 "5").value == 5
#guard numStr "5" == "integer:5"
#guard realStr "5" == "real:5.0"
#guard cnStr "5" == "integer:5"
#guard nvStr "5" == "integer:5"
#guard fmtReal (castToReal (.text "5")) == "5.0"
#guard (atoF ".").value.toBits == 0x0000000000000000
#guard (atoi64 ".").value == 0
#guard numStr "." == "text:."
#guard realStr "." == "text:."
#guard cnStr "." == "integer:0"
#guard nvStr "." == "integer:0"
#guard fmtReal (castToReal (.text ".")) == "0.0"
#guard (atoF "20.19328168858067944668180480").value.toBits == 0x4034317ae8a35ea3
#guard (atoi64 "20.19328168858067944668180480").value == 20
#guard numStr "20.19328168858067944668180480" == "real:20.193281688580679"
#guard realStr "20.19328168858067944668180480" == "real:20.193281688580679"
#guard cnStr "20.19328168858067944668180480" == "real:20.193281688580679"
#guard nvStr "20.19328168858067944668180480" == "real:20.193281688580679"
#guard fmtReal (castToReal (.text "20.19328168858067944668180480")) == "20.193281688580679"
#guard (atoF "8E").value.toBits == 0x4020000000000000
#guard (atoi64 "8E").value == 8
#guard numStr "8E" == "text:8E"
#guard realStr "8E" == "text:8E"
#guard cnStr "8E" == "integer:8"
#guard nvStr "8E" == "integer:8"
#guard fmtReal (castToReal (.text "8E")) == "8.0"
#guard (atoF "e-1e105- ").value.toBits == 0x0000000000000000
#guard (atoi64 "e-1e105- ").value == 0
#guard numStr "e-1e105- " == "text:e-1e105- "
#guard realStr "e-1e105- " == "text:e-1e105- "
#guard cnStr "e-1e105- " == "integer:0"
#guard nvStr "e-1e105- " == "integer:0"
#guard fmtReal (castToReal (.text "e-1e105- ")) == "0.0"
#guard (atoF "000303.").value.toBits == 0x4072f00000000000
#guard (atoi64 "000303.").value == 303
#guard numStr "000303." == "integer:303"
#guard realStr "000303." == "real:303.0"
#guard cnStr "000303." == "integer:303"
#guard nvStr "000303." == "real:303.0"
#guard fmtReal (castToReal (.text "000303.")) == "303.0"
#guard (atoF "0.101e10+").value.toBits == 0x41ce19b040000000
#guard (atoi64 "0.101e10+").value == 0
#guard numStr "0.101e10+" == "text:0.101e10+"
#guard realStr "0.101e10+" == "text:0.101e10+"
#guard cnStr "0.101e10+" == "integer:1010000000"
#guard nvStr "0.101e10+" == "real:1010000000.0"
#guard fmtReal (castToReal (.text "0.101e10+")) == "1010000000.0"
#guard (atoF "3992").value.toBits == 0x40af300000000000
#guard (atoi64 "3992").value == 3992
#guard numStr "3992" == "integer:3992"
#guard realStr "3992" == "real:3992.0"
#guard cnStr "3992" == "integer:3992"
#guard nvStr "3992" == "integer:3992"
#guard fmtReal (castToReal (.text "3992")) == "3992.0"
#guard (atoF "6130-").value.toBits == 0x40b7f20000000000
#guard (atoi64 "6130-").value == 6130
#guard numStr "6130-" == "text:6130-"
#guard realStr "6130-" == "text:6130-"
#guard cnStr "6130-" == "integer:6130"
#guard nvStr "6130-" == "integer:6130"
#guard fmtReal (castToReal (.text "6130-")) == "6130.0"
#guard (atoF "39125454\t922337203685477580").value.toBits == 0x4182a80e70000000
#guard (atoi64 "39125454\t922337203685477580").value == 39125454
#guard numStr "39125454\t922337203685477580" == "text:39125454\t922337203685477580"
#guard realStr "39125454\t922337203685477580" == "text:39125454\t922337203685477580"
#guard cnStr "39125454\t922337203685477580" == "integer:39125454"
#guard nvStr "39125454\t922337203685477580" == "integer:39125454"
#guard fmtReal (castToReal (.text "39125454\t922337203685477580")) == "39125454.0"
#guard (atoF "7179347507870532300").value.toBits == 0x43d8e88aa1516d61
#guard (atoi64 "7179347507870532300").value == 7179347507870532300
#guard numStr "7179347507870532300" == "integer:7179347507870532300"
#guard realStr "7179347507870532300" == "real:7.1793475078705326e+18"
#guard cnStr "7179347507870532300" == "integer:7179347507870532300"
#guard nvStr "7179347507870532300" == "integer:7179347507870532300"
#guard fmtReal (castToReal (.text "7179347507870532300")) == "7.1793475078705326e+18"
#guard (atoF "\t000").value.toBits == 0x0000000000000000
#guard (atoi64 "\t000").value == 0
#guard numStr "\t000" == "integer:0"
#guard realStr "\t000" == "real:0.0"
#guard cnStr "\t000" == "integer:0"
#guard nvStr "\t000" == "integer:0"
#guard fmtReal (castToReal (.text "\t000")) == "0.0"
#guard (atoF " e8.922").value.toBits == 0x0000000000000000
#guard (atoi64 " e8.922").value == 0
#guard numStr " e8.922" == "text: e8.922"
#guard realStr " e8.922" == "text: e8.922"
#guard cnStr " e8.922" == "integer:0"
#guard nvStr " e8.922" == "integer:0"
#guard fmtReal (castToReal (.text " e8.922")) == "0.0"
#guard (atoF "002+295\n").value.toBits == 0x4000000000000000
#guard (atoi64 "002+295\n").value == 2
#guard numStr "002+295\n" == "text:002+295\n"
#guard realStr "002+295\n" == "text:002+295\n"
#guard cnStr "002+295\n" == "integer:2"
#guard nvStr "002+295\n" == "integer:2"
#guard fmtReal (castToReal (.text "002+295\n")) == "2.0"
#guard (atoF "5").value.toBits == 0x4014000000000000
#guard (atoi64 "5").value == 5
#guard numStr "5" == "integer:5"
#guard realStr "5" == "real:5.0"
#guard cnStr "5" == "integer:5"
#guard nvStr "5" == "integer:5"
#guard fmtReal (castToReal (.text "5")) == "5.0"
#guard (atoF ". 80282786205130424").value.toBits == 0x0000000000000000
#guard (atoi64 ". 80282786205130424").value == 0
#guard numStr ". 80282786205130424" == "text:. 80282786205130424"
#guard realStr ". 80282786205130424" == "text:. 80282786205130424"
#guard cnStr ". 80282786205130424" == "integer:0"
#guard nvStr ". 80282786205130424" == "integer:0"
#guard fmtReal (castToReal (.text ". 80282786205130424")) == "0.0"
#guard (atoF "307688340906058917").value.toBits == 0x43911483a9d4f093
#guard (atoi64 "307688340906058917").value == 307688340906058917
#guard numStr "307688340906058917" == "integer:307688340906058917"
#guard realStr "307688340906058917" == "real:3.0768834090605894e+17"
#guard cnStr "307688340906058917" == "integer:307688340906058917"
#guard nvStr "307688340906058917" == "integer:307688340906058917"
#guard fmtReal (castToReal (.text "307688340906058917")) == "3.0768834090605894e+17"
#guard (atoF "4580e-").value.toBits == 0x40b1e40000000000
#guard (atoi64 "4580e-").value == 4580
#guard numStr "4580e-" == "text:4580e-"
#guard realStr "4580e-" == "text:4580e-"
#guard cnStr "4580e-" == "integer:4580"
#guard nvStr "4580e-" == "integer:4580"
#guard fmtReal (castToReal (.text "4580e-")) == "4580.0"
#guard (atoF "-00").value.toBits == 0x8000000000000000
#guard (atoi64 "-00").value == 0
#guard numStr "-00" == "integer:0"
#guard realStr "-00" == "real:0.0"
#guard cnStr "-00" == "integer:0"
#guard nvStr "-00" == "integer:0"
#guard fmtReal (castToReal (.text "-00")) == "0.0"
#guard (atoF "624").value.toBits == 0x4083800000000000
#guard (atoi64 "624").value == 624
#guard numStr "624" == "integer:624"
#guard realStr "624" == "real:624.0"
#guard cnStr "624" == "integer:624"
#guard nvStr "624" == "integer:624"
#guard fmtReal (castToReal (.text "624")) == "624.0"
#guard (atoF "900").value.toBits == 0x408c200000000000
#guard (atoi64 "900").value == 900
#guard numStr "900" == "integer:900"
#guard realStr "900" == "real:900.0"
#guard cnStr "900" == "integer:900"
#guard nvStr "900" == "integer:900"
#guard fmtReal (castToReal (.text "900")) == "900.0"
#guard (atoF "826515988938").value.toBits == 0x42680e0624394000
#guard (atoi64 "826515988938").value == 826515988938
#guard numStr "826515988938" == "integer:826515988938"
#guard realStr "826515988938" == "real:826515988938.0"
#guard cnStr "826515988938" == "integer:826515988938"
#guard nvStr "826515988938" == "integer:826515988938"
#guard fmtReal (castToReal (.text "826515988938")) == "826515988938.0"
#guard (atoF "8464383479416289223372036854775808+25").value.toBits == 0x46fa1538a176325b
#guard (atoi64 "8464383479416289223372036854775808+25").value == 9223372036854775807
#guard numStr "8464383479416289223372036854775808+25" == "text:8464383479416289223372036854775808+25"
#guard realStr "8464383479416289223372036854775808+25" == "text:8464383479416289223372036854775808+25"
#guard cnStr "8464383479416289223372036854775808+25" == "real:8.4643834794162892e+33"
#guard nvStr "8464383479416289223372036854775808+25" == "real:8.4643834794162892e+33"
#guard fmtReal (castToReal (.text "8464383479416289223372036854775808+25")) == "8.4643834794162892e+33"
#guard (atoF "z.+98522620262148").value.toBits == 0x0000000000000000
#guard (atoi64 "z.+98522620262148").value == 0
#guard numStr "z.+98522620262148" == "text:z.+98522620262148"
#guard realStr "z.+98522620262148" == "text:z.+98522620262148"
#guard cnStr "z.+98522620262148" == "integer:0"
#guard nvStr "z.+98522620262148" == "integer:0"
#guard fmtReal (castToReal (.text "z.+98522620262148")) == "0.0"
#guard (atoF "781123970430966-47").value.toBits == 0x4306336cc643bfb0
#guard (atoi64 "781123970430966-47").value == 781123970430966
#guard numStr "781123970430966-47" == "text:781123970430966-47"
#guard realStr "781123970430966-47" == "text:781123970430966-47"
#guard cnStr "781123970430966-47" == "integer:781123970430966"
#guard nvStr "781123970430966-47" == "integer:781123970430966"
#guard fmtReal (castToReal (.text "781123970430966-47")) == "781123970430966.0"
#guard (atoF ".Ee-0").value.toBits == 0x0000000000000000
#guard (atoi64 ".Ee-0").value == 0
#guard numStr ".Ee-0" == "text:.Ee-0"
#guard realStr ".Ee-0" == "text:.Ee-0"
#guard cnStr ".Ee-0" == "integer:0"
#guard nvStr ".Ee-0" == "integer:0"
#guard fmtReal (castToReal (.text ".Ee-0")) == "0.0"
#guard (atoF "  .").value.toBits == 0x0000000000000000
#guard (atoi64 "  .").value == 0
#guard numStr "  ." == "text:  ."
#guard realStr "  ." == "text:  ."
#guard cnStr "  ." == "integer:0"
#guard nvStr "  ." == "integer:0"
#guard fmtReal (castToReal (.text "  .")) == "0.0"
#guard (atoF "4  1e109653419641868").value.toBits == 0x4010000000000000
#guard (atoi64 "4  1e109653419641868").value == 4
#guard numStr "4  1e109653419641868" == "text:4  1e109653419641868"
#guard realStr "4  1e109653419641868" == "text:4  1e109653419641868"
#guard cnStr "4  1e109653419641868" == "integer:4"
#guard nvStr "4  1e109653419641868" == "integer:4"
#guard fmtReal (castToReal (.text "4  1e109653419641868")) == "4.0"
#guard (atoF " xe").value.toBits == 0x0000000000000000
#guard (atoi64 " xe").value == 0
#guard numStr " xe" == "text: xe"
#guard realStr " xe" == "text: xe"
#guard cnStr " xe" == "integer:0"
#guard nvStr " xe" == "integer:0"
#guard fmtReal (castToReal (.text " xe")) == "0.0"
#guard (atoF "9223372036854775807\n54947").value.toBits == 0x43e0000000000000
#guard (atoi64 "9223372036854775807\n54947").value == 9223372036854775807
#guard numStr "9223372036854775807\n54947" == "text:9223372036854775807\n54947"
#guard realStr "9223372036854775807\n54947" == "text:9223372036854775807\n54947"
#guard cnStr "9223372036854775807\n54947" == "integer:9223372036854775807"
#guard nvStr "9223372036854775807\n54947" == "integer:9223372036854775807"
#guard fmtReal (castToReal (.text "9223372036854775807\n54947")) == "9.2233720368547758e+18"
#guard (atoF ".x108656374377485564700319").value.toBits == 0x0000000000000000
#guard (atoi64 ".x108656374377485564700319").value == 0
#guard numStr ".x108656374377485564700319" == "text:.x108656374377485564700319"
#guard realStr ".x108656374377485564700319" == "text:.x108656374377485564700319"
#guard cnStr ".x108656374377485564700319" == "integer:0"
#guard nvStr ".x108656374377485564700319" == "integer:0"
#guard fmtReal (castToReal (.text ".x108656374377485564700319")) == "0.0"

/-! ### Casts of reals and blobs -/

#guard castToInt (.real (Float.ofBits 0x3fe0000000000000)) == 0
#guard fmtReal (castToReal (.real (Float.ofBits 0x3fe0000000000000))) == "0.5"
#guard castToInt (.real (Float.ofBits 0x3ff8000000000000)) == 1
#guard fmtReal (castToReal (.real (Float.ofBits 0x3ff8000000000000))) == "1.5"
#guard castToInt (.real (Float.ofBits 0xbfe0000000000000)) == 0
#guard fmtReal (castToReal (.real (Float.ofBits 0xbfe0000000000000))) == "-0.5"
#guard castToInt (.real (Float.ofBits 0x4004000000000000)) == 2
#guard fmtReal (castToReal (.real (Float.ofBits 0x4004000000000000))) == "2.5"
#guard castToInt (.real (Float.ofBits 0x43abc16d674ec800)) == 1000000000000000000
#guard fmtReal (castToReal (.real (Float.ofBits 0x43abc16d674ec800))) == "1.0e+18"
#guard castToInt (.real (Float.ofBits 0x43e02207973f6440)) == 9223372036854775807
#guard fmtReal (castToReal (.real (Float.ofBits 0x43e02207973f6440))) == "9.3e+18"
#guard castToInt (.real (Float.ofBits 0xc3e02207973f6440)) == (-9223372036854775808)
#guard fmtReal (castToReal (.real (Float.ofBits 0xc3e02207973f6440))) == "-9.3e+18"
#guard castToInt (.real (Float.ofBits 0x43e0000000000000)) == 9223372036854775807
#guard fmtReal (castToReal (.real (Float.ofBits 0x43e0000000000000))) == "9.2233720368547758e+18"
#guard castToInt (.real (Float.ofBits 0xc3e0000000000000)) == (-9223372036854775808)
#guard fmtReal (castToReal (.real (Float.ofBits 0xc3e0000000000000))) == "-9.2233720368547758e+18"
#guard castToInt (.real (Float.ofBits 0x0000000000000001)) == 0
#guard fmtReal (castToReal (.real (Float.ofBits 0x0000000000000001))) == "4.9406564584124654e-324"
#guard castToInt (.real (Float.ofBits 0x405effef9db22d0e)) == 123
#guard fmtReal (castToReal (.real (Float.ofBits 0x405effef9db22d0e))) == "123.999"
#guard castToInt (.real (Float.ofBits 0xc05effef9db22d0e)) == (-123)
#guard fmtReal (castToReal (.real (Float.ofBits 0xc05effef9db22d0e))) == "-123.999"
#guard castToInt (.real (Float.ofBits 0x7e37e43c8800759c)) == 9223372036854775807
#guard fmtReal (castToReal (.real (Float.ofBits 0x7e37e43c8800759c))) == "1.0e+300"
#guard castToInt (.real (Float.ofBits 0x4008000000000000)) == 3
#guard fmtReal (castToReal (.real (Float.ofBits 0x4008000000000000))) == "3.0"
#guard castToInt (.real (Float.ofBits 0x8000000000000000)) == 0
#guard fmtReal (castToReal (.real (Float.ofBits 0x8000000000000000))) == "0.0"
#guard castToInt (.real (Float.ofBits 0x0000000000000000)) == 0
#guard fmtReal (castToReal (.real (Float.ofBits 0x0000000000000000))) == "0.0"
#guard castToInt (.real (Float.ofBits 0x43dfffffffffffff)) == 9223372036854774784
#guard fmtReal (castToReal (.real (Float.ofBits 0x43dfffffffffffff))) == "9.2233720368547748e+18"
#guard castToInt (.real (Float.ofBits 0x43dfffffffffffff)) == 9223372036854774784
#guard fmtReal (castToReal (.real (Float.ofBits 0x43dfffffffffffff))) == "9.2233720368547748e+18"
#guard castToInt (.real (Float.ofBits 0x43e158e460913d00)) == 9223372036854775807
#guard fmtReal (castToReal (.real (Float.ofBits 0x43e158e460913d00))) == "1.0e+19"
#guard castToInt (.real (Float.ofBits 0xc3e158e460913d00)) == (-9223372036854775808)
#guard fmtReal (castToReal (.real (Float.ofBits 0xc3e158e460913d00))) == "-1.0e+19"
#guard castToInt (.real (Float.ofBits 0x7fefffffffffffff)) == 9223372036854775807
#guard fmtReal (castToReal (.real (Float.ofBits 0x7fefffffffffffff))) == "1.7976931348623157e+308"
#guard castToInt (.real (Float.ofBits 0x7ff0000000000000)) == 9223372036854775807
#guard fmtReal (castToReal (.real (Float.ofBits 0x7ff0000000000000))) == "Inf"
#guard castToInt (.real (Float.ofBits 0xfff0000000000000)) == (-9223372036854775808)
#guard fmtReal (castToReal (.real (Float.ofBits 0xfff0000000000000))) == "-Inf"
#guard castToInt (.real (Float.ofBits 0x44031f3216adfa59)) == 9223372036854775807
#guard fmtReal (castToReal (.real (Float.ofBits 0x44031f3216adfa59))) == "4.4092002687622259e+19"
#guard castToInt (.real (Float.ofBits 0x43c2d5d91011ff00)) == 2714459051533402112
#guard fmtReal (castToReal (.real (Float.ofBits 0x43c2d5d91011ff00))) == "2.7144590515334021e+18"
#guard castToInt (.real (Float.ofBits 0xc21dc6765f0fa3d7)) == (-31970924483)
#guard fmtReal (castToReal (.real (Float.ofBits 0xc21dc6765f0fa3d7))) == "-31970924483.91"
#guard castToInt (.real (Float.ofBits 0x4147f0e447783f2c)) == 3137992
#guard fmtReal (castToReal (.real (Float.ofBits 0x4147f0e447783f2c))) == "3137992.5583571401"
#guard castToInt (.real (Float.ofBits 0xc185743ea589dfef)) == (-44992468)
#guard fmtReal (castToReal (.real (Float.ofBits 0xc185743ea589dfef))) == "-44992468.692321651"
#guard castToInt (.real (Float.ofBits 0xbec070c9ecbd72d3)) == 0
#guard fmtReal (castToReal (.real (Float.ofBits 0xbec070c9ecbd72d3))) == "-1.959869996000189e-06"
#guard castToInt (.real (Float.ofBits 0x3f96257f0c4e38a7)) == 0
#guard fmtReal (castToReal (.real (Float.ofBits 0x3f96257f0c4e38a7))) == "0.021627411962577139"
#guard castToInt (.real (Float.ofBits 0xc06569da118ffc01)) == (-171)
#guard fmtReal (castToReal (.real (Float.ofBits 0xc06569da118ffc01))) == "-171.30786970254852"
#guard castToInt (.real (Float.ofBits 0x3e084ff75b9e4a2e)) == 0
#guard fmtReal (castToReal (.real (Float.ofBits 0x3e084ff75b9e4a2e))) == "7.07583040108899e-10"
#guard castToInt (.real (Float.ofBits 0x44588939600e9617)) == 9223372036854775807
#guard fmtReal (castToReal (.real (Float.ofBits 0x44588939600e9617))) == "1.8104395913666471e+21"
#guard castToInt (.real (Float.ofBits 0x3e9c592a898ba031)) == 0
#guard fmtReal (castToReal (.real (Float.ofBits 0x3e9c592a898ba031))) == "4.2242266710826921e-07"
#guard castToInt (.real (Float.ofBits 0xc4c06525bc9fe664)) == (-9223372036854775808)
#guard fmtReal (castToReal (.real (Float.ofBits 0xc4c06525bc9fe664))) == "-1.5484740820289176e+23"
#guard castToInt (.real (Float.ofBits 0xc38f1fe6996682ae)) == (-280345585747252672)
#guard fmtReal (castToReal (.real (Float.ofBits 0xc38f1fe6996682ae))) == "-2.8034558574725267e+17"
#guard castToInt (.real (Float.ofBits 0xc4307e5098b116e1)) == (-9223372036854775808)
#guard fmtReal (castToReal (.real (Float.ofBits 0xc4307e5098b116e1))) == "-3.0424984791262908e+20"
#guard castToInt (.real (Float.ofBits 0xc37b9526a7b8dba9)) == (-124221082022296208)
#guard fmtReal (castToReal (.real (Float.ofBits 0xc37b9526a7b8dba9))) == "-1.2422108202229621e+17"
#guard castToInt (.real (Float.ofBits 0xc06035184e130355)) == (-129)
#guard fmtReal (castToReal (.real (Float.ofBits 0xc06035184e130355))) == "-129.65921691621284"
#guard castToInt (.real (Float.ofBits 0xbe63e879e47ec66c)) == 0
#guard fmtReal (castToReal (.real (Float.ofBits 0xbe63e879e47ec66c))) == "-3.7081744396784708e-08"
#guard castToInt (.real (Float.ofBits 0x40da54f0c2646c88)) == 26963
#guard fmtReal (castToReal (.real (Float.ofBits 0x40da54f0c2646c88))) == "26963.761864763248"
#guard castToInt (.real (Float.ofBits 0x42c2129c8af53805)) == 39742290127472
#guard fmtReal (castToReal (.real (Float.ofBits 0x42c2129c8af53805))) == "39742290127472.039"
#guard castToInt (.real (Float.ofBits 0xbe34539a113b1271)) == 0
#guard fmtReal (castToReal (.real (Float.ofBits 0xbe34539a113b1271))) == "-4.7326482903557752e-09"
#guard castToInt (.real (Float.ofBits 0xc133b5580d8d0b2c)) == (-1291608)
#guard fmtReal (castToReal (.real (Float.ofBits 0xc133b5580d8d0b2c))) == "-1291608.0529334052"
#guard castToInt (.real (Float.ofBits 0x4319b4340307733a)) == 1808752474971342
#guard fmtReal (castToReal (.real (Float.ofBits 0x4319b4340307733a))) == "1808752474971342.5"
#guard castToInt (.real (Float.ofBits 0x42986e78b0762c5d)) == 6715687574923
#guard fmtReal (castToReal (.real (Float.ofBits 0x42986e78b0762c5d))) == "6715687574923.0908"
#guard castToInt (.real (Float.ofBits 0xbf988144648fbb60)) == 0
#guard fmtReal (castToReal (.real (Float.ofBits 0xbf988144648fbb60))) == "-0.023930615079673756"
#guard castToInt (.real (Float.ofBits 0xc4ffa6fad09a3fa2)) == (-9223372036854775808)
#guard fmtReal (castToReal (.real (Float.ofBits 0xc4ffa6fad09a3fa2))) == "-2.3915774976015603e+24"
#guard castToInt (.real (Float.ofBits 0xc1c0e1d5fb2a0b45)) == (-566471670)
#guard fmtReal (castToReal (.real (Float.ofBits 0xc1c0e1d5fb2a0b45))) == "-566471670.32846892"
#guard castToInt (.real (Float.ofBits 0x3ed20576a823479a)) == 0
#guard fmtReal (castToReal (.real (Float.ofBits 0x3ed20576a823479a))) == "4.2966227075824478e-06"
#guard castToInt (.real (Float.ofBits 0xbfa580ce0291b0a0)) == 0
#guard fmtReal (castToReal (.real (Float.ofBits 0xbfa580ce0291b0a0))) == "-0.041998327077494624"
#guard castToInt (.real (Float.ofBits 0xbef92eab208846c6)) == 0
#guard fmtReal (castToReal (.real (Float.ofBits 0xbef92eab208846c6))) == "-2.4015711490638405e-05"
#guard castToInt (.real (Float.ofBits 0x40307def3fdec279)) == 16
#guard fmtReal (castToReal (.real (Float.ofBits 0x40307def3fdec279))) == "16.491931907543833"
#guard castToInt (.real (Float.ofBits 0x43c023411a8a495e)) == 2325689422073478144
#guard fmtReal (castToReal (.real (Float.ofBits 0x43c023411a8a495e))) == "2.3256894220734781e+18"
#guard castToInt (.real (Float.ofBits 0xbebafc29d7742a2c)) == 0
#guard fmtReal (castToReal (.real (Float.ofBits 0xbebafc29d7742a2c))) == "-1.6084321410892546e-06"
#guard castToInt (.real (Float.ofBits 0x3f6f9e91e96f0a0a)) == 0
#guard fmtReal (castToReal (.real (Float.ofBits 0x3f6f9e91e96f0a0a))) == "0.0038597917404967807"
#guard castToInt (.real (Float.ofBits 0xc2157413ea7b64e1)) == (-23035443870)
#guard fmtReal (castToReal (.real (Float.ofBits 0xc2157413ea7b64e1))) == "-23035443870.848515"
#guard castToInt (.real (Float.ofBits 0xbf39e9351dceedec)) == 0
#guard fmtReal (castToReal (.real (Float.ofBits 0xbf39e9351dceedec))) == "-0.00039536997592978687"
#guard castToInt (.real (Float.ofBits 0xc1d01b283d24775f)) == (-1080860916)
#guard fmtReal (castToReal (.real (Float.ofBits 0xc1d01b283d24775f))) == "-1080860916.5697858"
#guard castToInt (.real (Float.ofBits 0x3e6a1a8d9d571356)) == 0
#guard fmtReal (castToReal (.real (Float.ofBits 0x3e6a1a8d9d571356))) == "4.8621973707267817e-08"
#guard castToInt (.blob (ByteArray.mk #[])) == 0
#guard fmtReal (castToReal (.blob (ByteArray.mk #[]))) == "0.0"
#guard showV (castToNumeric (.blob (ByteArray.mk #[]))) == "integer:0"
#guard showV (numericValue (.blob (ByteArray.mk #[]))) == "integer:0"
#guard castToInt (.blob (ByteArray.mk #[0x31])) == 1
#guard fmtReal (castToReal (.blob (ByteArray.mk #[0x31]))) == "1.0"
#guard showV (castToNumeric (.blob (ByteArray.mk #[0x31]))) == "integer:1"
#guard showV (numericValue (.blob (ByteArray.mk #[0x31]))) == "integer:1"
#guard castToInt (.blob (ByteArray.mk #[0x31, 0x32])) == 12
#guard fmtReal (castToReal (.blob (ByteArray.mk #[0x31, 0x32]))) == "12.0"
#guard showV (castToNumeric (.blob (ByteArray.mk #[0x31, 0x32]))) == "integer:12"
#guard showV (numericValue (.blob (ByteArray.mk #[0x31, 0x32]))) == "integer:12"
#guard castToInt (.blob (ByteArray.mk #[0x31, 0x32, 0x7a])) == 12
#guard fmtReal (castToReal (.blob (ByteArray.mk #[0x31, 0x32, 0x7a]))) == "12.0"
#guard showV (castToNumeric (.blob (ByteArray.mk #[0x31, 0x32, 0x7a]))) == "integer:12"
#guard showV (numericValue (.blob (ByteArray.mk #[0x31, 0x32, 0x7a]))) == "integer:12"
#guard castToInt (.blob (ByteArray.mk #[0x2d, 0x30, 0x30, 0x37, 0x2e, 0x35])) == (-7)
#guard fmtReal (castToReal (.blob (ByteArray.mk #[0x2d, 0x30, 0x30, 0x37, 0x2e, 0x35]))) == "-7.5"
#guard showV (castToNumeric (.blob (ByteArray.mk #[0x2d, 0x30, 0x30, 0x37, 0x2e, 0x35]))) == "real:-7.5"
#guard showV (numericValue (.blob (ByteArray.mk #[0x2d, 0x30, 0x30, 0x37, 0x2e, 0x35]))) == "real:-7.5"
#guard castToInt (.blob (ByteArray.mk #[0x31, 0x65, 0x2b, 0x32])) == 1
#guard fmtReal (castToReal (.blob (ByteArray.mk #[0x31, 0x65, 0x2b, 0x32]))) == "100.0"
#guard showV (castToNumeric (.blob (ByteArray.mk #[0x31, 0x65, 0x2b, 0x32]))) == "integer:100"
#guard showV (numericValue (.blob (ByteArray.mk #[0x31, 0x65, 0x2b, 0x32]))) == "real:100.0"
#guard castToInt (.blob (ByteArray.mk #[0x20, 0x20, 0x20, 0x33])) == 3
#guard fmtReal (castToReal (.blob (ByteArray.mk #[0x20, 0x20, 0x20, 0x33]))) == "3.0"
#guard showV (castToNumeric (.blob (ByteArray.mk #[0x20, 0x20, 0x20, 0x33]))) == "integer:3"
#guard showV (numericValue (.blob (ByteArray.mk #[0x20, 0x20, 0x20, 0x33]))) == "integer:3"
#guard castToInt (.blob (ByteArray.mk #[0xff, 0x31])) == 0
#guard fmtReal (castToReal (.blob (ByteArray.mk #[0xff, 0x31]))) == "0.0"
#guard showV (castToNumeric (.blob (ByteArray.mk #[0xff, 0x31]))) == "integer:0"
#guard showV (numericValue (.blob (ByteArray.mk #[0xff, 0x31]))) == "integer:0"
#guard castToInt (.blob (ByteArray.mk #[0x00])) == 0
#guard fmtReal (castToReal (.blob (ByteArray.mk #[0x00]))) == "0.0"
#guard showV (castToNumeric (.blob (ByteArray.mk #[0x00]))) == "integer:0"
#guard showV (numericValue (.blob (ByteArray.mk #[0x00]))) == "integer:0"
#guard castToInt (.blob (ByteArray.mk #[0x61, 0x62])) == 0
#guard fmtReal (castToReal (.blob (ByteArray.mk #[0x61, 0x62]))) == "0.0"
#guard showV (castToNumeric (.blob (ByteArray.mk #[0x61, 0x62]))) == "integer:0"
#guard showV (numericValue (.blob (ByteArray.mk #[0x61, 0x62]))) == "integer:0"
#guard castToInt (.blob (ByteArray.mk #[0x39, 0x2e, 0x35, 0x23])) == 9
#guard fmtReal (castToReal (.blob (ByteArray.mk #[0x39, 0x2e, 0x35, 0x23]))) == "9.5"
#guard showV (castToNumeric (.blob (ByteArray.mk #[0x39, 0x2e, 0x35, 0x23]))) == "real:9.5"
#guard showV (numericValue (.blob (ByteArray.mk #[0x39, 0x2e, 0x35, 0x23]))) == "real:9.5"
#guard castToInt (.blob (ByteArray.mk #[0x30, 0x78, 0x31])) == 0
#guard fmtReal (castToReal (.blob (ByteArray.mk #[0x30, 0x78, 0x31]))) == "0.0"
#guard showV (castToNumeric (.blob (ByteArray.mk #[0x30, 0x78, 0x31]))) == "integer:0"
#guard showV (numericValue (.blob (ByteArray.mk #[0x30, 0x78, 0x31]))) == "integer:0"
#guard cmpI 0 0x3fe0000000000000 == -1
#guard cmpI 0 0xc3e02207973f6440 == 1
#guard cmpI 0 0x7e37e43c8800759c == -1
#guard cmpI 0 0x43e158e460913d00 == -1
#guard cmpI 0 0x43c2d5d91011ff00 == -1
#guard cmpI 0 0xc06569da118ffc01 == 1
#guard cmpI 0 0xc4307e5098b116e1 == 1
#guard cmpI 1 0xbfe0000000000000 == 1
#guard cmpI 1 0xc3e0000000000000 == 1
#guard cmpI 1 0x8000000000000000 == 1
#guard cmpI 1 0x7fefffffffffffff == -1
#guard cmpI 1 0x4147f0e447783f2c == -1
#guard cmpI 1 0x44588939600e9617 == -1
#guard cmpI 1 0xc06035184e130355 == 1
#guard cmpI (-1) 0x43abc16d674ec800 == -1
#guard cmpI (-1) 0x405effef9db22d0e == -1
#guard cmpI (-1) 0x43dfffffffffffff == -1
#guard cmpI (-1) 0xfff0000000000000 == 1
#guard cmpI (-1) 0xbec070c9ecbd72d3 == -1
#guard cmpI (-1) 0xc4c06525bc9fe664 == 1
#guard cmpI 5 0x3fe0000000000000 == 1
#guard cmpI 5 0xc3e02207973f6440 == 1
#guard cmpI 5 0x7e37e43c8800759c == -1
#guard cmpI 5 0x43e158e460913d00 == -1
#guard cmpI 5 0x43c2d5d91011ff00 == -1
#guard cmpI 5 0xc06569da118ffc01 == 1
#guard cmpI 5 0xc4307e5098b116e1 == 1
#guard cmpI 9223372036854775807 0xbfe0000000000000 == 1
#guard cmpI 9223372036854775807 0xc3e0000000000000 == 1
#guard cmpI 9223372036854775807 0x8000000000000000 == 1
#guard cmpI 9223372036854775807 0x7fefffffffffffff == -1
#guard cmpI 9223372036854775807 0x4147f0e447783f2c == 1
#guard cmpI 9223372036854775807 0x44588939600e9617 == -1
#guard cmpI 9223372036854775807 0xc06035184e130355 == 1
#guard cmpI (-9223372036854775808) 0x43abc16d674ec800 == -1
#guard cmpI (-9223372036854775808) 0x405effef9db22d0e == -1
#guard cmpI (-9223372036854775808) 0x43dfffffffffffff == -1
#guard cmpI (-9223372036854775808) 0xfff0000000000000 == 1
#guard cmpI (-9223372036854775808) 0xbec070c9ecbd72d3 == -1
#guard cmpI (-9223372036854775808) 0xc4c06525bc9fe664 == 1
#guard cmpI 9007199254740993 0x3fe0000000000000 == 1
#guard cmpI 9007199254740993 0xc3e02207973f6440 == 1
#guard cmpI 9007199254740993 0x7e37e43c8800759c == -1
#guard cmpI 9007199254740993 0x43e158e460913d00 == -1
#guard cmpI 9007199254740993 0x43c2d5d91011ff00 == -1
#guard cmpI 9007199254740993 0xc06569da118ffc01 == 1
#guard cmpI 9007199254740993 0xc4307e5098b116e1 == 1
#guard cmpI 9007199254740992 0xbfe0000000000000 == 1
#guard cmpI 9007199254740992 0xc3e0000000000000 == 1
#guard cmpI 9007199254740992 0x8000000000000000 == 1
#guard cmpI 9007199254740992 0x7fefffffffffffff == -1
#guard cmpI 9007199254740992 0x4147f0e447783f2c == 1
#guard cmpI 9007199254740992 0x44588939600e9617 == -1
#guard cmpI 9007199254740992 0xc06035184e130355 == 1
#guard cmpI (-9007199254740993) 0x43abc16d674ec800 == -1
#guard cmpI (-9007199254740993) 0x405effef9db22d0e == -1
#guard cmpI (-9007199254740993) 0x43dfffffffffffff == -1
#guard cmpI (-9007199254740993) 0xfff0000000000000 == 1
#guard cmpI (-9007199254740993) 0xbec070c9ecbd72d3 == -1
#guard cmpI (-9007199254740993) 0xc4c06525bc9fe664 == 1
#guard cmpI 9223372036854774784 0x3fe0000000000000 == 1
#guard cmpI 9223372036854774784 0xc3e02207973f6440 == 1
#guard cmpI 9223372036854774784 0x7e37e43c8800759c == -1
#guard cmpI 9223372036854774784 0x43e158e460913d00 == -1
#guard cmpI 9223372036854774784 0x43c2d5d91011ff00 == 1
#guard cmpI 9223372036854774784 0xc06569da118ffc01 == 1
#guard cmpI 9223372036854774784 0xc4307e5098b116e1 == 1
#guard cmpI 9223372036854774785 0xbfe0000000000000 == 1
#guard cmpI 9223372036854774785 0xc3e0000000000000 == 1
#guard cmpI 9223372036854774785 0x8000000000000000 == 1
#guard cmpI 9223372036854774785 0x7fefffffffffffff == -1
#guard cmpI 9223372036854774785 0x4147f0e447783f2c == 1
#guard cmpI 9223372036854774785 0x44588939600e9617 == -1
#guard cmpI 9223372036854774785 0xc06035184e130355 == 1
#guard cmpI 123456789012345678 0x43abc16d674ec800 == -1
#guard cmpI 123456789012345678 0x405effef9db22d0e == 1
#guard cmpI 123456789012345678 0x43dfffffffffffff == -1
#guard cmpI 123456789012345678 0xfff0000000000000 == 1
#guard cmpI 123456789012345678 0xbec070c9ecbd72d3 == 1
#guard cmpI 123456789012345678 0xc4c06525bc9fe664 == 1
#guard cmpI 4611686018427387904 0x3fe0000000000000 == 1
#guard cmpI 4611686018427387904 0xc3e02207973f6440 == 1
#guard cmpI 4611686018427387904 0x7e37e43c8800759c == -1
#guard cmpI 4611686018427387904 0x43e158e460913d00 == -1
#guard cmpI 4611686018427387904 0x43c2d5d91011ff00 == 1
#guard cmpI 4611686018427387904 0xc06569da118ffc01 == 1
#guard cmpI 4611686018427387904 0xc4307e5098b116e1 == 1
#guard cmpI (-159794885337495780) 0xc381bda4d00bb9c7 == -1
#guard cmpI (-452938367550698304) 0xc39924a42e9c04cd == 0
#guard cmpI (-1123715578034458570) 0xc3af307abaa2a21f == -1
#guard cmpI 157870795977055166 0x438186f53854f6de == -1
#guard cmpI (-74219862888357450) 0xc3707ae9272bd1e5 == 1
#guard cmpI 2088270913888679808 0x43bcfb0755011d78 == -1
#guard cmpI 384185972398226250 0x4395539c6cf1efed == 1
#guard cmpI (-1171313935139273360) 0xc3b04157d17070fb == 1
#guard cmpI 145628084958959680 0x43802affc60a64c3 == -1
#guard cmpI (-170456870798624456) 0xc382ecacf78bd036 == -1
#guard cmpI 1070887346756167161 0x43adb91cbc73b94c == -1
#guard cmpI 57741059322884100 0x4369a466003ca5fe == 1
#guard cmpI (-73897175943928445) 0xc370689170a0ada8 == 1
#guard cmpI (-2921275023423042005) 0xc3c4453a13ff2cf9 == 1
#guard cmpI (-242752609918882635) 0xc38af371b3541c9a == -1
#guard cmpI 1036494715922533710 0x43acc4bce7b4439b == -1
#guard cmpI 62708971887439130 0x436bd92f493295a3 == 1
#guard cmpI 2748194728741503591 0x43c311c645ca1e81 == 1
#guard cmpI (-3182947590407584131) 0xc3c6160cfc1876fc == -1
#guard cmpI 1203238196978500572 0x43b0b2c2c3df15c0 == 1
#guard cmpI (-841295844346087296) 0xc3a759c439e2858f == 0
#guard cmpI 1650154593871648350 0x43b6e686dc3832d4 == 1
#guard cmpI (-2408691595212121975) 0xc3c0b6b21f3d0b34 == 1
#guard cmpI (-445403280495445875) 0xc398b98fb1eee61e == 1
#guard cmpI (-1540532122201949800) 0xc3b56111cd94ed06 == -1
#guard cmpI (-2065823659102118844) 0xc3bcab47ac396124 == 1
#guard cmpI 1859693500519187190 0x43b9cef562b98c83 == -1
#guard cmpI (-1403192792090731960) 0xc3b3792468f3f4e6 == 1
#guard cmpI 1677642854278514772 0x43b7482f49953e48 == 1
#guard cmpI 903951737258838768 0x43a916f6a1a2d216 == -1
#guard cmpI (-2809571099502603810) 0xc3c37ecd03be8737 == -1
#guard cmpI 1976345200752546282 0x43bb6d637d2c6750 == 1
#guard cmpI 3488522113110374967 0x43c834dc307f84fd == 1
#guard arithStr (addInt? 0 0) == "0"
#guard arithStr (addInt? 0 4294967296) == "4294967296"
#guard arithStr (addInt? 1 (-9223372036854775808)) == "-9223372036854775807"
#guard arithStr (addInt? (-1) (-2)) == "-3"
#guard arithStr (addInt? (-1) 1000000007) == "1000000006"
#guard arithStr (addInt? 2 (-3037000500)) == "-3037000498"
#guard arithStr (addInt? (-2) 9223372036854775807) == "9223372036854775805"
#guard arithStr (addInt? 3 (-1)) == "2"
#guard arithStr (addInt? 3 2147483648) == "2147483651"
#guard arithStr (addInt? 7 (-4611686018427387904)) == "-4611686018427387897"
#guard arithStr (addInt? (-7) 7) == "0"
#guard arithStr (addInt? 9223372036854775807 0) == "9223372036854775807"
#guard arithStr (addInt? 9223372036854775807 4294967296) == "none"
#guard arithStr (addInt? (-9223372036854775807) (-9223372036854775808)) == "none"
#guard arithStr (addInt? (-9223372036854775808) (-2)) == "none"
#guard arithStr (addInt? (-9223372036854775808) 1000000007) == "-9223372035854775801"
#guard arithStr (addInt? 4611686018427387904 (-3037000500)) == "4611686015390387404"
#guard arithStr (addInt? (-4611686018427387904) 9223372036854775807) == "4611686018427387903"
#guard arithStr (addInt? 3037000500 (-1)) == "3037000499"
#guard arithStr (addInt? 3037000500 2147483648) == "5184484148"
#guard arithStr (addInt? (-3037000500) (-4611686018427387904)) == "-4611686021464388404"
#guard arithStr (addInt? 3037000499 7) == "3037000506"
#guard arithStr (addInt? 4294967296 0) == "4294967296"
#guard arithStr (addInt? 4294967296 4294967296) == "8589934592"
#guard arithStr (addInt? (-4294967296) (-9223372036854775808)) == "none"
#guard arithStr (addInt? 2147483648 (-2)) == "2147483646"
#guard arithStr (addInt? 2147483648 1000000007) == "3147483655"
#guard arithStr (addInt? 100 (-3037000500)) == "-3037000400"
#guard arithStr (addInt? 1000000007 9223372036854775807) == "none"
#guard arithStr (addInt? 9223372036854775806 (-1)) == "9223372036854775805"
#guard arithStr (addInt? 9223372036854775806 2147483648) == "none"
#guard arithStr (subInt? 0 (-4611686018427387904)) == "4611686018427387904"
#guard arithStr (subInt? 1 7) == "-6"
#guard arithStr (subInt? (-1) 0) == "-1"
#guard arithStr (subInt? (-1) 4294967296) == "-4294967297"
#guard arithStr (subInt? 2 (-9223372036854775808)) == "none"
#guard arithStr (subInt? (-2) (-2)) == "0"
#guard arithStr (subInt? (-2) 1000000007) == "-1000000009"
#guard arithStr (subInt? 3 (-3037000500)) == "3037000503"
#guard arithStr (subInt? 7 9223372036854775807) == "-9223372036854775800"
#guard arithStr (subInt? (-7) (-1)) == "-6"
#guard arithStr (subInt? (-7) 2147483648) == "-2147483655"
#guard arithStr (subInt? 9223372036854775807 (-4611686018427387904)) == "none"
#guard arithStr (subInt? (-9223372036854775807) 7) == "none"
#guard arithStr (subInt? (-9223372036854775808) 0) == "-9223372036854775808"
#guard arithStr (subInt? (-9223372036854775808) 4294967296) == "none"
#guard arithStr (subInt? 4611686018427387904 (-9223372036854775808)) == "none"
#guard arithStr (subInt? (-4611686018427387904) (-2)) == "-4611686018427387902"
#guard arithStr (subInt? (-4611686018427387904) 1000000007) == "-4611686019427387911"
#guard arithStr (subInt? 3037000500 (-3037000500)) == "6074001000"
#guard arithStr (subInt? (-3037000500) 9223372036854775807) == "none"
#guard arithStr (subInt? 3037000499 (-1)) == "3037000500"
#guard arithStr (subInt? 3037000499 2147483648) == "889516851"
#guard arithStr (subInt? 4294967296 (-4611686018427387904)) == "4611686022722355200"
#guard arithStr (subInt? (-4294967296) 7) == "-4294967303"
#guard arithStr (subInt? 2147483648 0) == "2147483648"
#guard arithStr (subInt? 2147483648 4294967296) == "-2147483648"
#guard arithStr (subInt? 100 (-9223372036854775808)) == "none"
#guard arithStr (subInt? 1000000007 (-2)) == "1000000009"
#guard arithStr (subInt? 1000000007 1000000007) == "0"
#guard arithStr (subInt? 9223372036854775806 (-3037000500)) == "none"
#guard arithStr (mulInt? 0 9223372036854775807) == "0"
#guard arithStr (mulInt? 1 (-1)) == "-1"
#guard arithStr (mulInt? 1 2147483648) == "2147483648"
#guard arithStr (mulInt? (-1) (-4611686018427387904)) == "4611686018427387904"
#guard arithStr (mulInt? 2 7) == "14"
#guard arithStr (mulInt? (-2) 0) == "0"
#guard arithStr (mulInt? (-2) 4294967296) == "-8589934592"
#guard arithStr (mulInt? 3 (-9223372036854775808)) == "none"
#guard arithStr (mulInt? 7 (-2)) == "-14"
#guard arithStr (mulInt? 7 1000000007) == "7000000049"
#guard arithStr (mulInt? (-7) (-3037000500)) == "21259003500"
#guard arithStr (mulInt? 9223372036854775807 9223372036854775807) == "none"
#guard arithStr (mulInt? (-9223372036854775807) (-1)) == "9223372036854775807"
#guard arithStr (mulInt? (-9223372036854775807) 2147483648) == "none"
#guard arithStr (mulInt? (-9223372036854775808) (-4611686018427387904)) == "none"
#guard arithStr (mulInt? 4611686018427387904 7) == "none"
#guard arithStr (mulInt? (-4611686018427387904) 0) == "0"
#guard arithStr (mulInt? (-4611686018427387904) 4294967296) == "none"
#guard arithStr (mulInt? 3037000500 (-9223372036854775808)) == "none"
#guard arithStr (mulInt? (-3037000500) (-2)) == "6074001000"
#guard arithStr (mulInt? (-3037000500) 1000000007) == "-3037000521259003500"
#guard arithStr (mulInt? 3037000499 (-3037000500)) == "-9223372033963249500"
#guard arithStr (mulInt? 4294967296 9223372036854775807) == "none"
#guard arithStr (mulInt? (-4294967296) (-1)) == "4294967296"
#guard arithStr (mulInt? (-4294967296) 2147483648) == "-9223372036854775808"
#guard arithStr (mulInt? 2147483648 (-4611686018427387904)) == "none"
#guard arithStr (mulInt? 100 7) == "700"
#guard arithStr (mulInt? 1000000007 0) == "0"
#guard arithStr (mulInt? 1000000007 4294967296) == "4294967326064771072"
#guard arithStr (mulInt? 9223372036854775806 (-9223372036854775808)) == "none"
#guard arithStr (divInt? 0 (-2)) == "0"
#guard arithStr (divInt? 0 1000000007) == "0"
#guard arithStr (divInt? 1 (-3037000500)) == "0"
#guard arithStr (divInt? (-1) 9223372036854775807) == "0"
#guard arithStr (divInt? 2 (-1)) == "-2"
#guard arithStr (divInt? 2 2147483648) == "0"
#guard arithStr (divInt? (-2) (-4611686018427387904)) == "0"
#guard arithStr (divInt? 3 7) == "0"
#guard arithStr (divInt? 7 0) == "none"
#guard arithStr (divInt? 7 4294967296) == "0"
#guard arithStr (divInt? (-7) (-9223372036854775808)) == "0"
#guard arithStr (divInt? 9223372036854775807 (-2)) == "-4611686018427387903"
#guard arithStr (divInt? 9223372036854775807 1000000007) == "9223371972"
#guard arithStr (divInt? (-9223372036854775807) (-3037000500)) == "3037000499"
#guard arithStr (divInt? (-9223372036854775808) 9223372036854775807) == "-1"
#guard arithStr (divInt? 4611686018427387904 (-1)) == "-4611686018427387904"
#guard arithStr (divInt? 4611686018427387904 2147483648) == "2147483648"
#guard arithStr (divInt? (-4611686018427387904) (-4611686018427387904)) == "1"
#guard arithStr (divInt? 3037000500 7) == "433857214"
#guard arithStr (divInt? (-3037000500) 0) == "none"
#guard arithStr (divInt? (-3037000500) 4294967296) == "0"
#guard arithStr (divInt? 3037000499 (-9223372036854775808)) == "0"
#guard arithStr (divInt? 4294967296 (-2)) == "-2147483648"
#guard arithStr (divInt? 4294967296 1000000007) == "4"
#guard arithStr (divInt? (-4294967296) (-3037000500)) == "1"
#guard arithStr (divInt? 2147483648 9223372036854775807) == "0"
#guard arithStr (divInt? 100 (-1)) == "-100"
#guard arithStr (divInt? 100 2147483648) == "0"
#guard arithStr (divInt? 1000000007 (-4611686018427387904)) == "0"
#guard arithStr (divInt? 9223372036854775806 7) == "1317624576693539400"
#guard arithStr (remInt? 0 0) == "none"
#guard arithStr (remInt? 0 4294967296) == "0"
#guard arithStr (remInt? 1 (-9223372036854775808)) == "1"
#guard arithStr (remInt? (-1) (-2)) == "-1"
#guard arithStr (remInt? (-1) 1000000007) == "-1"
#guard arithStr (remInt? 2 (-3037000500)) == "2"
#guard arithStr (remInt? (-2) 9223372036854775807) == "-2"
#guard arithStr (remInt? 3 (-1)) == "0"
#guard arithStr (remInt? 3 2147483648) == "3"
#guard arithStr (remInt? 7 (-4611686018427387904)) == "7"
#guard arithStr (remInt? (-7) 7) == "0"
#guard arithStr (remInt? 9223372036854775807 0) == "none"
#guard arithStr (remInt? 9223372036854775807 4294967296) == "4294967295"
#guard arithStr (remInt? (-9223372036854775807) (-9223372036854775808)) == "-9223372036854775807"
#guard arithStr (remInt? (-9223372036854775808) (-2)) == "0"
#guard arithStr (remInt? (-9223372036854775808) 1000000007) == "-291172004"
#guard arithStr (remInt? 4611686018427387904 (-3037000500)) == "2964263404"
#guard arithStr (remInt? (-4611686018427387904) 9223372036854775807) == "-4611686018427387904"
#guard arithStr (remInt? 3037000500 (-1)) == "0"
#guard arithStr (remInt? 3037000500 2147483648) == "889516852"
#guard arithStr (remInt? (-3037000500) (-4611686018427387904)) == "-3037000500"
#guard arithStr (remInt? 3037000499 7) == "1"
#guard arithStr (remInt? 4294967296 0) == "none"
#guard arithStr (remInt? 4294967296 4294967296) == "0"
#guard arithStr (remInt? (-4294967296) (-9223372036854775808)) == "-4294967296"
#guard arithStr (remInt? 2147483648 (-2)) == "0"
#guard arithStr (remInt? 2147483648 1000000007) == "147483634"
#guard arithStr (remInt? 100 (-3037000500)) == "100"
#guard arithStr (remInt? 1000000007 9223372036854775807) == "1000000007"

/-! ### round() -/
#guard fmtReal (roundReal (Float.ofBits 0x3fe0000000000000) 0) == "1.0"
#guard fmtReal (roundReal (Float.ofBits 0x3fe0000000000000) 1) == "0.5"
#guard fmtReal (roundReal (Float.ofBits 0x3fe0000000000000) 2) == "0.5"
#guard fmtReal (roundReal (Float.ofBits 0x3fe0000000000000) 5) == "0.5"
#guard fmtReal (roundReal (Float.ofBits 0x3fe0000000000000) 30) == "0.5"
#guard fmtReal (roundReal (Float.ofBits 0x3fe0000000000000) 35) == "0.5"
#guard fmtReal (roundReal (Float.ofBits 0x3fe0000000000000) (-3)) == "1.0"
#guard fmtReal (roundReal (Float.ofBits 0x3ff8000000000000) 0) == "2.0"
#guard fmtReal (roundReal (Float.ofBits 0x3ff8000000000000) 1) == "1.5"
#guard fmtReal (roundReal (Float.ofBits 0x3ff8000000000000) 2) == "1.5"
#guard fmtReal (roundReal (Float.ofBits 0x3ff8000000000000) 5) == "1.5"
#guard fmtReal (roundReal (Float.ofBits 0x3ff8000000000000) 30) == "1.5"
#guard fmtReal (roundReal (Float.ofBits 0x3ff8000000000000) 35) == "1.5"
#guard fmtReal (roundReal (Float.ofBits 0x3ff8000000000000) (-3)) == "2.0"
#guard fmtReal (roundReal (Float.ofBits 0x4004000000000000) 0) == "3.0"
#guard fmtReal (roundReal (Float.ofBits 0x4004000000000000) 1) == "2.5"
#guard fmtReal (roundReal (Float.ofBits 0x4004000000000000) 2) == "2.5"
#guard fmtReal (roundReal (Float.ofBits 0x4004000000000000) 5) == "2.5"
#guard fmtReal (roundReal (Float.ofBits 0x4004000000000000) 30) == "2.5"
#guard fmtReal (roundReal (Float.ofBits 0x4004000000000000) 35) == "2.5"
#guard fmtReal (roundReal (Float.ofBits 0x4004000000000000) (-3)) == "3.0"
#guard fmtReal (roundReal (Float.ofBits 0xbfe0000000000000) 0) == "-1.0"
#guard fmtReal (roundReal (Float.ofBits 0xbfe0000000000000) 1) == "-0.5"
#guard fmtReal (roundReal (Float.ofBits 0xbfe0000000000000) 2) == "-0.5"
#guard fmtReal (roundReal (Float.ofBits 0xbfe0000000000000) 5) == "-0.5"
#guard fmtReal (roundReal (Float.ofBits 0xbfe0000000000000) 30) == "-0.5"
#guard fmtReal (roundReal (Float.ofBits 0xbfe0000000000000) 35) == "-0.5"
#guard fmtReal (roundReal (Float.ofBits 0xbfe0000000000000) (-3)) == "-1.0"
#guard fmtReal (roundReal (Float.ofBits 0xbff8000000000000) 0) == "-2.0"
#guard fmtReal (roundReal (Float.ofBits 0xbff8000000000000) 1) == "-1.5"
#guard fmtReal (roundReal (Float.ofBits 0xbff8000000000000) 2) == "-1.5"
#guard fmtReal (roundReal (Float.ofBits 0xbff8000000000000) 5) == "-1.5"
#guard fmtReal (roundReal (Float.ofBits 0xbff8000000000000) 30) == "-1.5"
#guard fmtReal (roundReal (Float.ofBits 0xbff8000000000000) 35) == "-1.5"
#guard fmtReal (roundReal (Float.ofBits 0xbff8000000000000) (-3)) == "-2.0"
#guard fmtReal (roundReal (Float.ofBits 0x3fdccccccccccccd) 0) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x3fdccccccccccccd) 1) == "0.5"
#guard fmtReal (roundReal (Float.ofBits 0x3fdccccccccccccd) 2) == "0.45"
#guard fmtReal (roundReal (Float.ofBits 0x3fdccccccccccccd) 5) == "0.45"
#guard fmtReal (roundReal (Float.ofBits 0x3fdccccccccccccd) 30) == "0.45"
#guard fmtReal (roundReal (Float.ofBits 0x3fdccccccccccccd) 35) == "0.45"
#guard fmtReal (roundReal (Float.ofBits 0x3fdccccccccccccd) (-3)) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x3fe199999999999a) 0) == "1.0"
#guard fmtReal (roundReal (Float.ofBits 0x3fe199999999999a) 1) == "0.6"
#guard fmtReal (roundReal (Float.ofBits 0x3fe199999999999a) 2) == "0.55"
#guard fmtReal (roundReal (Float.ofBits 0x3fe199999999999a) 5) == "0.55"
#guard fmtReal (roundReal (Float.ofBits 0x3fe199999999999a) 30) == "0.55"
#guard fmtReal (roundReal (Float.ofBits 0x3fe199999999999a) 35) == "0.55"
#guard fmtReal (roundReal (Float.ofBits 0x3fe199999999999a) (-3)) == "1.0"
#guard fmtReal (roundReal (Float.ofBits 0x4005666666666666) 0) == "3.0"
#guard fmtReal (roundReal (Float.ofBits 0x4005666666666666) 1) == "2.7"
#guard fmtReal (roundReal (Float.ofBits 0x4005666666666666) 2) == "2.67"
#guard fmtReal (roundReal (Float.ofBits 0x4005666666666666) 5) == "2.675"
#guard fmtReal (roundReal (Float.ofBits 0x4005666666666666) 30) == "2.675"
#guard fmtReal (roundReal (Float.ofBits 0x4005666666666666) 35) == "2.675"
#guard fmtReal (roundReal (Float.ofBits 0x4005666666666666) (-3)) == "3.0"
#guard fmtReal (roundReal (Float.ofBits 0x3ff0147ae147ae14) 0) == "1.0"
#guard fmtReal (roundReal (Float.ofBits 0x3ff0147ae147ae14) 1) == "1.0"
#guard fmtReal (roundReal (Float.ofBits 0x3ff0147ae147ae14) 2) == "1.0"
#guard fmtReal (roundReal (Float.ofBits 0x3ff0147ae147ae14) 5) == "1.005"
#guard fmtReal (roundReal (Float.ofBits 0x3ff0147ae147ae14) 30) == "1.005"
#guard fmtReal (roundReal (Float.ofBits 0x3ff0147ae147ae14) 35) == "1.005"
#guard fmtReal (roundReal (Float.ofBits 0x3ff0147ae147ae14) (-3)) == "1.0"
#guard fmtReal (roundReal (Float.ofBits 0x405edd2f1a9fbe77) 0) == "123.0"
#guard fmtReal (roundReal (Float.ofBits 0x405edd2f1a9fbe77) 1) == "123.5"
#guard fmtReal (roundReal (Float.ofBits 0x405edd2f1a9fbe77) 2) == "123.46"
#guard fmtReal (roundReal (Float.ofBits 0x405edd2f1a9fbe77) 5) == "123.456"
#guard fmtReal (roundReal (Float.ofBits 0x405edd2f1a9fbe77) 30) == "123.456"
#guard fmtReal (roundReal (Float.ofBits 0x405edd2f1a9fbe77) 35) == "123.456"
#guard fmtReal (roundReal (Float.ofBits 0x405edd2f1a9fbe77) (-3)) == "123.0"
#guard fmtReal (roundReal (Float.ofBits 0xc05edd2f1a9fbe77) 0) == "-123.0"
#guard fmtReal (roundReal (Float.ofBits 0xc05edd2f1a9fbe77) 1) == "-123.5"
#guard fmtReal (roundReal (Float.ofBits 0xc05edd2f1a9fbe77) 2) == "-123.46"
#guard fmtReal (roundReal (Float.ofBits 0xc05edd2f1a9fbe77) 5) == "-123.456"
#guard fmtReal (roundReal (Float.ofBits 0xc05edd2f1a9fbe77) 30) == "-123.456"
#guard fmtReal (roundReal (Float.ofBits 0xc05edd2f1a9fbe77) 35) == "-123.456"
#guard fmtReal (roundReal (Float.ofBits 0xc05edd2f1a9fbe77) (-3)) == "-123.0"
#guard fmtReal (roundReal (Float.ofBits 0x0000000000000000) 0) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x0000000000000000) 1) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x0000000000000000) 2) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x0000000000000000) 5) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x0000000000000000) 30) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x0000000000000000) 35) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x0000000000000000) (-3)) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x430c6bf526340000) 0) == "1000000000000000.0"
#guard fmtReal (roundReal (Float.ofBits 0x430c6bf526340000) 1) == "1000000000000000.0"
#guard fmtReal (roundReal (Float.ofBits 0x430c6bf526340000) 2) == "1000000000000000.0"
#guard fmtReal (roundReal (Float.ofBits 0x430c6bf526340000) 5) == "1000000000000000.0"
#guard fmtReal (roundReal (Float.ofBits 0x430c6bf526340000) 30) == "1000000000000000.0"
#guard fmtReal (roundReal (Float.ofBits 0x430c6bf526340000) 35) == "1000000000000000.0"
#guard fmtReal (roundReal (Float.ofBits 0x430c6bf526340000) (-3)) == "1000000000000000.0"
#guard fmtReal (roundReal (Float.ofBits 0x4330000000000000) 0) == "4503599627370496.0"
#guard fmtReal (roundReal (Float.ofBits 0x4330000000000000) 1) == "4503599627370496.0"
#guard fmtReal (roundReal (Float.ofBits 0x4330000000000000) 2) == "4503599627370496.0"
#guard fmtReal (roundReal (Float.ofBits 0x4330000000000000) 5) == "4503599627370496.0"
#guard fmtReal (roundReal (Float.ofBits 0x4330000000000000) 30) == "4503599627370496.0"
#guard fmtReal (roundReal (Float.ofBits 0x4330000000000000) 35) == "4503599627370496.0"
#guard fmtReal (roundReal (Float.ofBits 0x4330000000000000) (-3)) == "4503599627370496.0"
#guard fmtReal (roundReal (Float.ofBits 0x4330000000000001) 0) == "4503599627370497.0"
#guard fmtReal (roundReal (Float.ofBits 0x4330000000000001) 1) == "4503599627370497.0"
#guard fmtReal (roundReal (Float.ofBits 0x4330000000000001) 2) == "4503599627370497.0"
#guard fmtReal (roundReal (Float.ofBits 0x4330000000000001) 5) == "4503599627370497.0"
#guard fmtReal (roundReal (Float.ofBits 0x4330000000000001) 30) == "4503599627370497.0"
#guard fmtReal (roundReal (Float.ofBits 0x4330000000000001) 35) == "4503599627370497.0"
#guard fmtReal (roundReal (Float.ofBits 0x4330000000000001) (-3)) == "4503599627370497.0"
#guard fmtReal (roundReal (Float.ofBits 0x432fffffffffffff) 0) == "4503599627370496.0"
#guard fmtReal (roundReal (Float.ofBits 0x432fffffffffffff) 1) == "4503599627370495.5"
#guard fmtReal (roundReal (Float.ofBits 0x432fffffffffffff) 2) == "4503599627370495.5"
#guard fmtReal (roundReal (Float.ofBits 0x432fffffffffffff) 5) == "4503599627370495.5"
#guard fmtReal (roundReal (Float.ofBits 0x432fffffffffffff) 30) == "4503599627370495.5"
#guard fmtReal (roundReal (Float.ofBits 0x432fffffffffffff) 35) == "4503599627370495.5"
#guard fmtReal (roundReal (Float.ofBits 0x432fffffffffffff) (-3)) == "4503599627370496.0"
#guard fmtReal (roundReal (Float.ofBits 0x3fd3333333333333) 0) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x3fd3333333333333) 1) == "0.3"
#guard fmtReal (roundReal (Float.ofBits 0x3fd3333333333333) 2) == "0.3"
#guard fmtReal (roundReal (Float.ofBits 0x3fd3333333333333) 5) == "0.3"
#guard fmtReal (roundReal (Float.ofBits 0x3fd3333333333333) 30) == "0.3"
#guard fmtReal (roundReal (Float.ofBits 0x3fd3333333333333) 35) == "0.3"
#guard fmtReal (roundReal (Float.ofBits 0x3fd3333333333333) (-3)) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x3fc3333333333333) 0) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x3fc3333333333333) 1) == "0.1"
#guard fmtReal (roundReal (Float.ofBits 0x3fc3333333333333) 2) == "0.15"
#guard fmtReal (roundReal (Float.ofBits 0x3fc3333333333333) 5) == "0.15"
#guard fmtReal (roundReal (Float.ofBits 0x3fc3333333333333) 30) == "0.15"
#guard fmtReal (roundReal (Float.ofBits 0x3fc3333333333333) 35) == "0.15"
#guard fmtReal (roundReal (Float.ofBits 0x3fc3333333333333) (-3)) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x3fd0000000000000) 0) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x3fd0000000000000) 1) == "0.3"
#guard fmtReal (roundReal (Float.ofBits 0x3fd0000000000000) 2) == "0.25"
#guard fmtReal (roundReal (Float.ofBits 0x3fd0000000000000) 5) == "0.25"
#guard fmtReal (roundReal (Float.ofBits 0x3fd0000000000000) 30) == "0.25"
#guard fmtReal (roundReal (Float.ofBits 0x3fd0000000000000) 35) == "0.25"
#guard fmtReal (roundReal (Float.ofBits 0x3fd0000000000000) (-3)) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x4058ffae147ae148) 0) == "100.0"
#guard fmtReal (roundReal (Float.ofBits 0x4058ffae147ae148) 1) == "100.0"
#guard fmtReal (roundReal (Float.ofBits 0x4058ffae147ae148) 2) == "100.0"
#guard fmtReal (roundReal (Float.ofBits 0x4058ffae147ae148) 5) == "99.995"
#guard fmtReal (roundReal (Float.ofBits 0x4058ffae147ae148) 30) == "99.995"
#guard fmtReal (roundReal (Float.ofBits 0x4058ffae147ae148) 35) == "99.995"
#guard fmtReal (roundReal (Float.ofBits 0x4058ffae147ae148) (-3)) == "100.0"
#guard fmtReal (roundReal (Float.ofBits 0x3fd3333333333334) 0) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x3fd3333333333334) 1) == "0.3"
#guard fmtReal (roundReal (Float.ofBits 0x3fd3333333333334) 2) == "0.3"
#guard fmtReal (roundReal (Float.ofBits 0x3fd3333333333334) 5) == "0.3"
#guard fmtReal (roundReal (Float.ofBits 0x3fd3333333333334) 30) == "0.30000000000000004"
#guard fmtReal (roundReal (Float.ofBits 0x3fd3333333333334) 35) == "0.30000000000000004"
#guard fmtReal (roundReal (Float.ofBits 0x3fd3333333333334) (-3)) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x3fd5555555555555) 0) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x3fd5555555555555) 1) == "0.3"
#guard fmtReal (roundReal (Float.ofBits 0x3fd5555555555555) 2) == "0.33"
#guard fmtReal (roundReal (Float.ofBits 0x3fd5555555555555) 5) == "0.33333"
#guard fmtReal (roundReal (Float.ofBits 0x3fd5555555555555) 30) == "0.33333333333333332"
#guard fmtReal (roundReal (Float.ofBits 0x3fd5555555555555) 35) == "0.33333333333333332"
#guard fmtReal (roundReal (Float.ofBits 0x3fd5555555555555) (-3)) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x3fe5555555555555) 0) == "1.0"
#guard fmtReal (roundReal (Float.ofBits 0x3fe5555555555555) 1) == "0.7"
#guard fmtReal (roundReal (Float.ofBits 0x3fe5555555555555) 2) == "0.67"
#guard fmtReal (roundReal (Float.ofBits 0x3fe5555555555555) 5) == "0.66667"
#guard fmtReal (roundReal (Float.ofBits 0x3fe5555555555555) 30) == "0.66666666666666663"
#guard fmtReal (roundReal (Float.ofBits 0x3fe5555555555555) 35) == "0.66666666666666663"
#guard fmtReal (roundReal (Float.ofBits 0x3fe5555555555555) (-3)) == "1.0"
#guard fmtReal (roundReal (Float.ofBits 0x0000000000000001) 0) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x0000000000000001) 1) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x0000000000000001) 2) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x0000000000000001) 5) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x0000000000000001) 30) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x0000000000000001) 35) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x0000000000000001) (-3)) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0xbfd999999999999a) 0) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0xbfd999999999999a) 1) == "-0.4"
#guard fmtReal (roundReal (Float.ofBits 0xbfd999999999999a) 2) == "-0.4"
#guard fmtReal (roundReal (Float.ofBits 0xbfd999999999999a) 5) == "-0.4"
#guard fmtReal (roundReal (Float.ofBits 0xbfd999999999999a) 30) == "-0.4"
#guard fmtReal (roundReal (Float.ofBits 0xbfd999999999999a) 35) == "-0.4"
#guard fmtReal (roundReal (Float.ofBits 0xbfd999999999999a) (-3)) == "0.0"
#guard fmtReal (roundReal (Float.ofBits 0x3fdfffffffffffff) 0) == "1.0"
#guard fmtReal (roundReal (Float.ofBits 0x3fdfffffffffffff) 1) == "0.5"
#guard fmtReal (roundReal (Float.ofBits 0x3fdfffffffffffff) 2) == "0.5"
#guard fmtReal (roundReal (Float.ofBits 0x3fdfffffffffffff) 5) == "0.5"
#guard fmtReal (roundReal (Float.ofBits 0x3fdfffffffffffff) 30) == "0.49999999999999994"
#guard fmtReal (roundReal (Float.ofBits 0x3fdfffffffffffff) 35) == "0.49999999999999994"
#guard fmtReal (roundReal (Float.ofBits 0x3fdfffffffffffff) (-3)) == "1.0"
#guard fmtReal (roundReal (Float.ofBits 0xbfdfffffffffffff) 0) == "-1.0"
#guard fmtReal (roundReal (Float.ofBits 0xbfdfffffffffffff) 1) == "-0.5"
#guard fmtReal (roundReal (Float.ofBits 0xbfdfffffffffffff) 2) == "-0.5"
#guard fmtReal (roundReal (Float.ofBits 0xbfdfffffffffffff) 5) == "-0.5"
#guard fmtReal (roundReal (Float.ofBits 0xbfdfffffffffffff) 30) == "-0.49999999999999994"
#guard fmtReal (roundReal (Float.ofBits 0xbfdfffffffffffff) 35) == "-0.49999999999999994"
#guard fmtReal (roundReal (Float.ofBits 0xbfdfffffffffffff) (-3)) == "-1.0"
#guard fmtReal (roundReal (Float.ofBits 0x41678c29df9add3c) 0) == "12345679.0"
#guard fmtReal (roundReal (Float.ofBits 0x41678c29df9add3c) 1) == "12345679.0"
#guard fmtReal (roundReal (Float.ofBits 0x41678c29df9add3c) 2) == "12345678.99"
#guard fmtReal (roundReal (Float.ofBits 0x41678c29df9add3c) 5) == "12345678.98765"
#guard fmtReal (roundReal (Float.ofBits 0x41678c29df9add3c) 30) == "12345678.987654321"
#guard fmtReal (roundReal (Float.ofBits 0x41678c29df9add3c) 35) == "12345678.987654321"
#guard fmtReal (roundReal (Float.ofBits 0x41678c29df9add3c) (-3)) == "12345679.0"
#guard fmtReal (roundReal (Float.ofBits 0x7e37e43c8800759c) 0) == "1.0e+300"
#guard fmtReal (roundReal (Float.ofBits 0x7e37e43c8800759c) 1) == "1.0e+300"
#guard fmtReal (roundReal (Float.ofBits 0x7e37e43c8800759c) 2) == "1.0e+300"
#guard fmtReal (roundReal (Float.ofBits 0x7e37e43c8800759c) 5) == "1.0e+300"
#guard fmtReal (roundReal (Float.ofBits 0x7e37e43c8800759c) 30) == "1.0e+300"
#guard fmtReal (roundReal (Float.ofBits 0x7e37e43c8800759c) 35) == "1.0e+300"
#guard fmtReal (roundReal (Float.ofBits 0x7e37e43c8800759c) (-3)) == "1.0e+300"
#guard fmtReal (roundReal (Float.ofBits 0x400921fb54442d11) 0) == "3.0"
#guard fmtReal (roundReal (Float.ofBits 0x400921fb54442d11) 1) == "3.1"
#guard fmtReal (roundReal (Float.ofBits 0x400921fb54442d11) 2) == "3.14"
#guard fmtReal (roundReal (Float.ofBits 0x400921fb54442d11) 5) == "3.14159"
#guard fmtReal (roundReal (Float.ofBits 0x400921fb54442d11) 30) == "3.14159265358979"
#guard fmtReal (roundReal (Float.ofBits 0x400921fb54442d11) 35) == "3.14159265358979"
#guard fmtReal (roundReal (Float.ofBits 0x400921fb54442d11) (-3)) == "3.0"

/-! ### printf() -/
#guard printf "%d" [.int 42] == "42"
#guard printf "%5d|%-5d|%05d|%+d|% d" [.int 42, .int 42, .int 42, .int 42, .int 42] == "   42|42   |00042|+42| 42"
#guard printf "%,d|%,d|%,d" [.int 1234567, .int (-1234), .int 999] == "1,234,567|-1,234|999"
#guard printf "%x %X %o %#x %#X %#o %#x" [.int 255, .int 255, .int 8, .int 255, .int 255, .int 8, .int 0] == "ff FF 10 0xff 0XFF 010 0"
#guard printf "%s|%10s|%-10s|%.2s|%5.1s" [.text "hello", .text "hello", .text "hello", .text "hello", .text "hello"] == "hello|     hello|hello     |he|    h"
#guard printf "%q %Q %Q %w" [.text "it's", .text "it's", .null, .text "a\"b"] == "it''s 'it''s' NULL a\"\"b"
#guard printf "%c%c%c" [.int 65, .text "é", .text "xyz"] == "6éx"
#guard printf "%e|%E|%g|%G|%f" [.real (Float.ofBits 0x40c81cd6e631f8a1), .real (Float.ofBits 0x40c81cd6e631f8a1), .real (Float.ofBits 0x40c81cd6e631f8a1), .real (Float.ofBits 0x3ddb7cdfd9d7bdbb), .real (Float.ofBits 0x40c81cd6e631f8a1)] == "1.234568e+04|1.234568E+04|12345.7|1E-10|12345.678900"
#guard printf "%.3f|%.0f|%#.0f|%10.3f|%-10.3f|%+.2f" [.real (Float.ofBits 0x4000010624dd2f1b), .real (Float.ofBits 0x3fe0000000000000), .real (Float.ofBits 0x3fe0000000000000), .real (Float.ofBits 0x400921f9f01b866e), .real (Float.ofBits 0x400921f9f01b866e), .real (Float.ofBits 0x4000000000000000)] == "2.001|1|1.|     3.142|3.142     |+2.00"
#guard printf "%lld %llx %u" [.int 9223372036854775807, .int (-1), .int (-1)] == "9223372036854775807 ffffffffffffffff 18446744073709551615"
#guard printf "100%%" [] == "100%"
#guard printf "%!.3s|%.3s" [.text "日本語テスト", .text "abc"] == "日本語|abc"
#guard printf "%z|%3c|%*d|%-*d|%.*f" [.text "zz", .text "q", .int 6, .int 42, .int 6, .int 42, .int 2, .real (Float.ofBits 0x400921f9f01b866e)] == "zz|  q|    42|42    |3.14"
#guard printf "%r %r %r %r %r %r %r" [.int 1, .int 2, .int 3, .int 4, .int 11, .int 12, .int 21] == "1st 2nd 3rd 4th 11th 12th 21st"
#guard printf "%.10d|%+.5d|%010.3d" [.int 42, .int 7, .int (-5)] == "0000000042|+00007|-000000005"
#guard printf "%g %g %g %g %g" [.real (Float.ofBits 0x40f86a0000000000), .real (Float.ofBits 0x412e848000000000), .real (Float.ofBits 0x3f1a36e2eb1c432d), .real (Float.ofBits 0x3ee4f8b588e368f1), .real (Float.ofBits 0x419d6f3454000000)] == "100000 1e+06 0.0001 1e-05 1.23457e+08"
#guard printf "%#g %!g %!.10g %.0g" [.real (Float.ofBits 0x3ff0000000000000), .real (Float.ofBits 0x3ff0000000000000), .real (Float.ofBits 0x3fb999999999999a), .real (Float.ofBits 0x402e000000000000)] == "1.00000 1.0 0.1 2e+01"
#guard printf "%f %e %g" [.real (Float.ofBits 0x7e6ddd4baa009303), .real (Float.ofBits 0xfe6ddd4baa009303), .real (Float.ofBits 0x7e6ddd4baa009303)] == "10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000.000000 -1.000000e+301 1e+301"
#guard printf "%010f|%+f|% f" [.real (Float.ofBits 0x7e6ddd4baa009303), .real (Float.ofBits 0x7e6ddd4baa009303), .real (Float.ofBits 0x7e6ddd4baa009303)] == "10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000.000000|+10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000.000000| 10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000.000000"
#guard printf "%s %s %s" [.int 5, .real (Float.ofBits 0x4004000000000000), .real (Float.ofBits 0x4415af1d78b58c40)] == "5 2.5 1.0e+20"
#guard printf "%d %d %d" [.text "12abc", .real (Float.ofBits 0x400feb851eb851ec), .real (Float.ofBits 0xc00feb851eb851ec)] == "12 3 -3"
#guard printf "%d %s" [.int 1] == "1 "
#guard printf "%" [] == "%"
#guard printf "abc%" [.int 1] == "abc%"
#guard printf "%y %d" [.int 1, .int 2] == ""
#guard printf "%5%|%-5%|" [] == "    %|%    |"
#guard printf "%j %J %10j %!.2j" [.text "a\"b\\c\n", .text "é", .text "x", .text "日本語"] == "a\\\"b\\\\c\\n \"é\"          x 日本"
#guard printf "%#q %#Q %#Q" [.text "a'b\nc\\", .text "a\nb", .text "ab"] == "a''b\\u000ac\\\\ unistr('a\\u000ab') 'ab'"
#guard printf "%.2q|%.3Q|%!.2w" [.text "a'b'c", .text "x'yz", .text "日本語"] == "a''|'x''y'|日本"
#guard printf "%f|%e|%g|%010f|%+f|%-8f|" [.real (Float.ofBits 0x7ff0000000000000), .real (Float.ofBits 0xfff0000000000000), .real (Float.ofBits 0x7ff0000000000000), .real (Float.ofBits 0x7ff0000000000000), .real (Float.ofBits 0x7ff0000000000000), .real (Float.ofBits 0xfff0000000000000)] == "Inf|-Inf|Inf|9000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000.000000|+Inf|-Inf    |"
#guard printf "%#0.dé% *.x%-*.*%" [.text "a'b", .text "x\"y", .int 20] == "0é14%"
#guard printf "abc%-.z" [.int 5, .text " 12 "] == "abc"
#guard printf "abc% 08.g" [.null, .text "tab\there"] == "abc 0000000"
#guard pfHex "%.1w%+*q" [.text "é漢字z", .text "abc def"] == "c3284e554c4c29"
#guard pfHex "%+!.13c%0.4i%!*.2cé%!.14Q" [.blob (ByteArray.mk #[0x00])] == "00000000000000000000000000303030300000c3a94e554c4c"
#guard printf "é%#!.3llf% #i" [.blob (ByteArray.mk #[])] == "é0.0 0"
#guard printf "[%+008.15q" [.real (Float.ofBits 0x40fe240c9fbe76c9), .real (Float.ofBits 0x7e6ddd4baa009303), .blob (ByteArray.mk #[0xff])] == "[123456.789"
#guard printf "%gabc%!Q" [.real (Float.ofBits 0x0), .text "12abc", .text "0x1F", .text "back\\slash"] == "0abc'12abc'"
#guard printf " - % #0.9o%!u" [] == " - 0000000000"
#guard printf "% #0.12s% 0,*f%#w%-+.12s" [.int 65] == "65 0.000000(NULL)"
#guard printf "é%!,*.j%3llg" [] == "é  0"
#guard printf "%,p%,.*u%-+#u" [.real (Float.ofBits 0x3f202e7ef70994dd)] == "000"
#guard printf "%%%+6.3Qé% !e%- 006.p%+0.*e" [.blob (ByteArray.mk #[0xc3, 0xa9]), .blob (ByteArray.mk #[]), .int 12, .int 1] == "%  'é'é 0.0e+0000000C+0.0e+00"
#guard printf "%0,.11s%#,.*X%.s" [.text "back\\slash", .null, .int 42, .null] == "back\\slash0X2A"
#guard printf "%3T" [.real (Float.ofBits 0xfe6ddd4baa009303), .null, .blob (ByteArray.mk #[])] == ""
#guard printf "[%#!.*x" [] == "[0"
#guard printf "abc%0.5g - %+ !112.r" [] == "abc0 -                                                                                                              0th"
#guard printf "%.9r" [.real (Float.ofBits 0x3f202e7ef70994dd), .int 9223372036854775807, .real (Float.ofBits 0x54b249ad2594c37d)] == "0000000th"
#guard printf "%-.z" [.real (Float.ofBits 0x4345ee2a2eb5a5c4), .real (Float.ofBits 0x3f202e7ef70994dd), .real (Float.ofBits 0x0), .int 20] == ""
#guard printf " - %#,g%010T%0.13x" [.int 3, .int 1, .int 1, .text "hello"] == " - 3.00000"
#guard printf "%%%+#.11g%" [.real (Float.ofBits 0x4202a05f20000000), .int 1] == "%+10000000000.%"
#guard printf "% e%-E%+0s" [.int 65] == " 6.500000e+010.000000E+00"
#guard pfHex "]%.7d]%+ #,*.19f]%!,*.20c" [.text "", .blob (ByteArray.mk #[0x41, 0x42])] == "5d303030303030305d20302e303030303030303030303030303030303030305d0000000000000000000000000000000000000000"
#guard printf " - %-0*r" [.real (Float.ofBits 0x4058e00000000000), .blob (ByteArray.mk #[0x41]), .real (Float.ofBits 0x400921f9f01b866e), .text "x\"y"] == " - 0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000th"
#guard printf "%-,.e%*J% x%#!.f" [] == "0e+00null00.0"
#guard printf "%+E%-003r" [] == "+0.000000E+000th"
#guard printf "[%+18g%!*.16e - %*.*ex %.12e" [] == "[                +00.0e+00 - 0e+00x 0.000000000000e+00"
#guard printf "% 02qabc%-+ ,09.13g%+!,.*x" [.real (Float.ofBits 0x3e8421f5f40d8376)] == "1.5e-07abc 0       0"
#guard printf "%.8fabc% .8u%-0.17%%-!,.19r" [.null, .int (-9223372036854775807)] == "0.00000000abc9223372036854775809%00000000000000000th"
#guard printf "[%+0*.0f - %-+#f - %!*f" [.blob (ByteArray.mk #[0x41])] == "[+0 - +0.000000 - 0.0"
#guard printf "]%,.X%!0x" [.text "12abc", .text " 12 ", .text "3.7e1", .text "9999999999999999999"] == "]Cc"
#guard printf "%0ld%0u" [] == "00"
#guard printf "%-.20z%0.14u%- !.3d]% 0,.r" [.text "-5", .text "\x01ctl"] == "-500000000000000 000] 0th"
#guard printf "%%%,w%,.s" [.real (Float.ofBits 0x3e8421f5f40d8376), .real (Float.ofBits 0x400921f9f01b866e), .null, .real (Float.ofBits 0x3fe0000000000000)] == "%1.5e-07"
#guard pfHex "abc% !*.10s - %-,1.q[%014w%-*.c" [] == "616263202d20205b2020202020202020284e554c4c2900"
#guard printf "%-,5X%s%- #J" [.int 20, .real (Float.ofBits 0x7e6ddd4baa009303), .blob (ByteArray.mk #[0xc3, 0xa9]), .text "3.7e1"] == "14   1.0e+301\"é\""
#guard printf "%-!6.2n% ,12f]%!0*.*Q" [] == "    0.000000]"
#guard printf "%0,7u%-+0*.*e%+,J" [.text "3.7e1", .real (Float.ofBits 0x1), .int (-3)] == "0,000,003+0.000e+00null"
#guard printf "%+u% #06llc" [.text "a'b", .real (Float.ofBits 0x54b249ad2594c37d), .int 65] == "0     1"
#guard printf "%+#,*.9Gé%+ué%+#0s" [.real (Float.ofBits 0x4059000000000000), .int (-3)] == "                                                                                         -3.00000000é0é"
#guard printf "% 11.9u%s%+ #,25d" [.int (-42), .text "9999999999999999999"] == "184467440737095515749999999999999999999                        0"
#guard printf "%#!3w%0.g - %+0,.11E%-+*.17d" [.text "", .text "tab\there", .int 5, .real (Float.ofBits 0x0)] == "   0 - +5.00000000000E+00+00000000000000000"
#guard printf "%#f%+.*g" [.text "nl\nx"] == "0.000000+0"
#guard printf " - %005.*y%+.*sabc%!%" [.real (Float.ofBits 0x4059000000000000), .int 3, .int 42, .real (Float.ofBits 0x3e8421f5f40d8376)] == " - "
#guard printf "%,05.5G%#o" [.text "A"] == "000000"
#guard printf "%-+E%,1.g%,J%0*Q" [.null, .real (Float.ofBits 0x3fb999999999999a), .int 8, .int 65] == "+0.000000E+000.1\"8\"                                                             NULL"
#guard printf "[%-+!x" [.real (Float.ofBits 0x4345ee2a2eb5a5c4), .blob (ByteArray.mk #[0x41]), .null, .text "back\\slash"] == "[2bdc545d6b4b88"
#guard printf "%.8w" [.blob (ByteArray.mk #[0xc3, 0xa9]), .real (Float.ofBits 0x3f202e7ef70994dd), .int 8] == "é"
#guard printf "%+#!7.19r%-+ 0,.16p%-+ !.14s%#,12f" [.real (Float.ofBits 0x401c000000000000), .int 8] == "+00000000000000007th0000000000000008    0.000000"
#guard printf "%+!3X" [.real (Float.ofBits 0x0), .int (-3)] == "  0"
#guard printf "%-!.14x%.18g" [] == "000000000000000"
#guard printf "%+.j]%-+0J" [] == "]null"
#guard printf "%,3.9Q%%%11.*d" [.null, .text "é漢字z", .real (Float.ofBits 0x3fe0000000000000), .real (Float.ofBits 0x3fe0000000000000)] == "NULL%          0"
#guard printf "%- .12d%+,.6lg%+#.5s%" [.real (Float.ofBits 0xfe6ddd4baa009303), .int 0] == "-9223372036854775808+0%"
#guard printf "[%+*.20Q" [.text "A", .int 3, .text "nl\nx"] == "['3'"
#guard printf "]%.12lls%,*d%-026ls" [.null, .real (Float.ofBits 0xab2bff2ee48e0530)] == "]0                          "
#guard printf "%.12s" [.blob (ByteArray.mk #[]), .blob (ByteArray.mk #[0xff])] == ""
#guard printf "é%.g% 0E%-lls" [.int (-3), .blob (ByteArray.mk #[0x41, 0x42]), .text "0x1F"] == "é-3 0.000000E+000x1F"
#guard printf "%!.*Q%+,*.3e" [.text "😀x", .blob (ByteArray.mk #[0x41])] == "''+0.000e+00"
#guard printf "%!.dé% .e% .2s%#016w" [.real (Float.ofBits 0x54b249ad2594c37d)] == "9223372036854775807é 0e+00          (NULL)"
#guard printf "%+.*g" [.int 20, .text "a%b", .int (-42), .blob (ByteArray.mk #[])] == "+0"
#guard printf "%-,w% !*.T%*.G" [] == "(NULL)"
#guard printf "%#,*.*G[%- .*Q" [.real (Float.ofBits 0x3e8421f5f40d8376), .blob (ByteArray.mk #[0xc3, 0xa9])] == "0.["
#guard printf "%-lls[%0,.2i" [.real (Float.ofBits 0xc004000000000000), .real (Float.ofBits 0x4058e00000000000)] == "-2.5[99"
#guard printf " - %#*x" [.real (Float.ofBits 0xab2bff2ee48e0530), .real (Float.ofBits 0x4345ee2a2eb5a5c4)] == " - 0x2bdc545d6b4b88"
#guard printf "%- *.5eabc%-.9G%+!.8g%+!0.11z" [.int 42] == " 0.00000e+00                              abc0+0.0"
#guard printf "%%%.*X%+.*n" [] == "%0"
#guard printf "%0,.3G[% 04.16X%+!.o]%-+#0*.e" [.text "\x01ctl", .text "tab\there"] == "0[00000000000000000]+0.e+00"
#guard printf "%+11.*Q%#.4p%-!.18q%,09.o" [] == "           0000(NULL)000000000"
#guard printf "[%r%- %% !.o" [.text "日本", .int 20] == "[0th%24"
#guard printf "%!7.f%+,.*d%#,.*Qabc%f" [] == "    0.0+0abc0.000000"
#guard printf "%- 12p%-+ !0.r% ,g" [.real (Float.ofBits 0x400921f9f01b866e), .text "9999999999999999999", .null] == "3            9223372036854775807th 0"
#guard printf "%-.*e%-+0.7w]%+.i" [] == "0e+00(NULL)]+0"
#guard printf " - %0,*.*q%+ 26d" [.null] == " -                          0"
#guard printf "% 9.18x%%%#!0,r" [] == "000000000000000000%0th"
#guard printf "%.*llf[% *d" [.text "a%b"] == "0[ 0"
#guard printf "% 0j%02y%+,.3X" [.int 20, .blob (ByteArray.mk #[])] == "20"
#guard printf "%*J%0,u%#0.d%0,2.3g" [] == "null0000"
#guard printf "% e" [.real (Float.ofBits 0x1)] == " 4.940656e-324"
#guard printf "]%o%+!*w%%%!3n" [.blob (ByteArray.mk #[0x00]), .text "-5", .text "nl\nx"] == "]0nl\nx %"
#guard printf "%Eé%.*e%!9.20p" [.real (Float.ofBits 0x1), .int 20, .real (Float.ofBits 0x3f202e7ef70994dd), .int 65] == "4.940656E-324é1.23456000000000000000e-0400000000000000000041"
#guard printf " - %-#.*E%.*G" [.real (Float.ofBits 0x3fe0000000000000), .text "3.7e1"] == " - 4.E+010"
#guard printf "%-!e" [] == "0.0e+00"
#guard printf "%+ !.12q% .17f%-+0u" [] == "(NULL) 0.000000000000000000"
#guard printf "%J" [.int 12, .text "😀x"] == "\"12\""
#guard printf "%%%-!0,E%-o" [.null, .text ""] == "%0.0E+000"
#guard printf " - % %%#,r%w" [.real (Float.ofBits 0x4058e00000000000)] == " - %99th(NULL)"
#guard printf " - %-+ .c" [.text "3.7e1", .real (Float.ofBits 0x4059000000000000), .real (Float.ofBits 0x54b249ad2594c37d)] == " - 3"
#guard printf "]%+4.8c%.E" [.real (Float.ofBits 0x7e6ddd4baa009303)] == "]111111110E+00"
#guard printf "% 0.17d" [] == " 00000000000000000"
#guard printf "%#.9e" [.real (Float.ofBits 0x3e8421f5f40d8376), .blob (ByteArray.mk #[])] == "1.500000000e-07"
#guard printf " - %*.13i" [.text "hello", .int 3, .real (Float.ofBits 0xab2bff2ee48e0530)] == " - 0000000000003"
#guard printf "%8.r" [.real (Float.ofBits 0x54b249ad2594c37d)] == "9223372036854775807th"
#guard printf "%#0z" [] == ""
#guard printf "%+#!.16G%!*.20j%#9.18s" [.real (Float.ofBits 0xc004000000000000), .null, .real (Float.ofBits 0xc004000000000000), .real (Float.ofBits 0xab2bff2ee48e0530)] == "-2.500000000000000-2.5-1.0e-100"
#guard printf "x %-!e" [.null, .real (Float.ofBits 0xc004000000000000)] == "x 0.0e+00"
#guard printf "% .E%#0.7d%,X" [.blob (ByteArray.mk #[0x00]), .real (Float.ofBits 0x54b249ad2594c37d)] == " 0E+0092233720368547758070"
#guard pfHex "%0llz%.c" [.null] == "00"
#guard printf "abc%-4.18i%%%#!022c%+,.20i" [.blob (ByteArray.mk #[0x00]), .real (Float.ofBits 0x3e8421f5f40d8376), .int 8, .text "9999999999999999999"] == "abc000000000000000000%                     1+00,000,000,000,000,000,008"
#guard printf "%ls" [.real (Float.ofBits 0x4345ee2a2eb5a5c4), .null, .real (Float.ofBits 0x3e8421f5f40d8376), .int 9223372036854775807] == "12345678901234568.0"
#guard pfHex "abc%-+ *.10z%#.*i%-+#,4.c" [] == "6162633000202020"
#guard printf "% .4f% 5llr%#.11c" [.null, .real (Float.ofBits 0xab2bff2ee48e0530), .int (-42), .real (Float.ofBits 0x3fe0000000000000)] == " 0.0000  0th-----------"
#guard printf "]%!4g%0.*J%" [.blob (ByteArray.mk #[0xc3, 0xa9]), .int 0, .int 65, .text "nl\nx"] == "] 0.0\"\"%"
#guard printf "é%+ .f" [] == "é 0"
#guard printf "%-#,oé%09.2i" [.real (Float.ofBits 0x400921f9f01b866e), .real (Float.ofBits 0x4321c37937e08000), .text "", .real (Float.ofBits 0x4202a05f20000000)] == "03é2500000000000000"
#guard printf "[% .d%*.u%12d" [.int 42, .int 1] == "[ 420           0"
#guard printf "%+015.17dx % !.7J" [.real (Float.ofBits 0x40fe240c9fbe76c9), .text " 12 "] == "+00000000000123456x \" 12 \""
#guard printf "abc%#.10lln%%% ,J% q%" [.blob (ByteArray.mk #[0xc3, 0xa9])] == "abc%\"é\"(NULL)%"
#guard printf "é%-#5.17s%%%.*o" [.int 12, .real (Float.ofBits 0xab2bff2ee48e0530), .text "x\"y", .text "日本"] == "é12   %0"
#guard printf "% *f%*J%#!0%" [.null, .int 3] == " 3.000000null%"
#guard printf "%-.d%!1.*f" [] == "00.0"
#guard printf "%+*.2o% 7.u" [.blob (ByteArray.mk #[0x41])] == "00      0"
#guard printf "é%010.dx %-#06.0e%%%+ #.*z%-#.z" [] == "é0000000000x 0.e+00%"
#guard printf "%!0,.w" [.real (Float.ofBits 0x0), .real (Float.ofBits 0x401c000000000000)] == ""
#guard printf "%3.20g]%- #.4z" [.int (-9223372036854775807), .text "a'b", .text "abc def", .null] == "-9223372036854776000]a'b"
#guard printf "[%!d%!*.*lf" [.int 16, .int 65] == "[16                                                              0.0"
#guard printf "%,10%" [] == "         %"
#guard printf "%+#0*w% G" [] == "(NULL) 0"
#guard printf "%+e%5.d" [.real (Float.ofBits 0x1), .int 1, .text "3.7e1"] == "+4.940656e-324    1"
#guard printf "%%%!,.*d% 21.5u%0f" [.int 8, .int 1, .real (Float.ofBits 0xfe6ddd4baa009303), .int 42] == "%00,000,001  922337203685477580842.000000"
#guard printf "% .f%+0j%+28z" [.blob (ByteArray.mk #[0x00]), .real (Float.ofBits 0x4345ee2a2eb5a5c4)] == " 012345678901234568.0                            "
#guard printf "%#03.21d%c - %.s" [.int (-1), .int (-42), .int 42, .blob (ByteArray.mk #[0x41, 0x42])] == "-000000000000000000001- - "
#guard pfHex "%5.6c" [] == "000000000000"
#guard printf "%3q" [.real (Float.ofBits 0xc004000000000000), .real (Float.ofBits 0x4202a05f20000000)] == "-2.5"
#guard printf "abc%!Tabc%-.*w[% 0*.5i" [.null, .int 9223372036854775807, .blob (ByteArray.mk #[])] == "abc"
#guard printf "%#!.Q" [.text "nl\nx"] == "''"
#guard printf "%%%11o%+,Gx % d" [] == "%          0+0x  0"
#guard printf "é%-*T%+!010.11T%z" [.null, .null, .real (Float.ofBits 0x401c000000000000)] == "é"
#guard printf "é% 8.11f%!01c%- !0,*.z%+!.*f" [.text "a'b", .int (-9223372036854775807)] == "é 0.00000000000-+0.0"
#guard printf "%-0*.2x%" [.null, .int 20, .text "-5"] == "14%"
#guard pfHex "%+0i%!.3q%+.8c" [.real (Float.ofBits 0x3fb999999999999a)] == "2b30284e550000000000000000"
#guard printf "% #w%+ 0,1.T" [.text "back\\slash", .null, .int 16] == "back\\slash"
#guard printf "%%% #!.19c" [.text "é漢字z", .blob (ByteArray.mk #[0xc3, 0xa9]), .blob (ByteArray.mk #[0x00]), .int 20] == "%ééééééééééééééééééé"
#guard printf "abc%X%+.13%" [.int (-3), .null] == "abcFFFFFFFFFFFFFFFD%"
#guard printf "%,*.3q%" [] == "(NU%"
#guard printf "%+ #,022.18r%+#*.%" [.null, .int (-9223372036854775807), .real (Float.ofBits 0x40fe240c9fbe76c9), .int 0] == " 0000000000000000000th%"
#guard printf "%,13ll%%-#5%%*.j" [] == "            %%    "
#guard printf "%%%-#0.3Q%" [.real (Float.ofBits 0x4345ee2a2eb5a5c4)] == "%'123'%"
#guard printf " - %3.17p" [.blob (ByteArray.mk #[0xff])] == " - 00000000000000000"
#guard printf "%.r%+ #!0.2%%-,.4gx %!.s" [.text "日本", .text "3.7e1", .text "nl\nx", .real (Float.ofBits 0x4059000000000000)] == "0th%37x "
#guard printf "[% ,*ly% #.13s" [.text "12abc", .blob (ByteArray.mk #[0xc3, 0xa9]), .null, .int 20] == "["
#guard printf "% .J%-!9.*r" [.text "A"] == "\"\"0th      "
#guard printf "%-.5llj%0,.*e" [.int 65, .null] == "650e+00"
#guard printf "é%- .8fx %-+023.18fx %+#.7%% !022x" [] == "é 0.00000000x +0.000000000000000000  x %0000000000000000000000"
#guard printf "%8.*G%+0s[%!01E" [] == "       0[0.0E+00"
#guard printf "% ,G%#!1.*f%+*.*o" [.int (-3)] == "-30.00"
#guard printf "%#!lle" [.null] == "0.0e+00"
#guard printf "%- !,*zabc%-.19r" [.real (Float.ofBits 0xfe6ddd4baa009303), .blob (ByteArray.mk #[0x41]), .text "12abc", .null] == "Aabc00000000000000012th"
#guard printf "%+g%,.0jx %23s" [.text "A"] == "+0x                        "
#guard printf "%#9g%-+218lln%09.s" [] == "  0.00000         "
#guard printf "[%!0,.*Jé%-8.9e" [.null, .real (Float.ofBits 0x3e8421f5f40d8376), .text "abc def"] == "[\"\"é0.000000000e+00"
#guard printf "%!y" [.blob (ByteArray.mk #[0xff]), .blob (ByteArray.mk #[0xc3, 0xa9])] == ""
#guard printf "%,.*Qé%+.13E%+ !0,J" [.text "é漢字z", .int 255] == "''é+0.0000000000000E+00null"
#guard printf "%%%-0.g% 015X%+ 0.*f" [.blob (ByteArray.mk #[0x00]), .blob (ByteArray.mk #[]), .int 12] == "%0000000000000000 0.000000000000"
#guard pfHex "%0.17e%#.0c" [.blob (ByteArray.mk #[0xc3, 0xa9]), .blob (ByteArray.mk #[0x00]), .text " 12 "] == "302e3030303030303030303030303030303030652b303000"
#guard printf "%-+!0.*p%.10c" [.blob (ByteArray.mk #[0x41]), .blob (ByteArray.mk #[0xc3, 0xa9]), .text "3.7e1"] == "03333333333"
#guard printf "%+,.wx %-+ #!0.15%%+#012.E%#,6.3%" [] == "x %+000000.E+00     %"
#guard printf "]%,Q%*s%,.*j" [.text "日本", .int 16, .int 20] == "]'日本'              20"
#guard printf "%#,c%3.J" [.text "tab\there", .int 42, .real (Float.ofBits 0x7e6ddd4baa009303)] == "t \"\""
#guard pfHex "%.*f%-+0.12j[%.*c" [.text " 12 ", .null] == "302e3030303030303030303030305b00"
#guard printf "%%%+ fabc%018.s]%-!.p" [.int (-1), .text "a%b", .text "😀x", .text "3.7e1"] == "%-1.000000abc                  ]0"
#guard pfHex "%+#!.u%%%-!s%2.2c" [.null, .int (-1)] == "30252d310000"
#guard printf "%-,015.20s" [] == "               "
#guard printf "%,e%!.10G" [.null, .int (-42), .real (Float.ofBits 0x54b249ad2594c37d)] == "0.000000e+00-42.0"
#guard printf "%!24.*i" [.null, .int 12, .int (-3), .text "日本"] == "                      12"
#guard printf "%r" [.real (Float.ofBits 0x3fb999999999999a), .text "a%b", .real (Float.ofBits 0xab2bff2ee48e0530), .int 65] == "0th"
#guard printf "%+.*Q" [.real (Float.ofBits 0x7e6ddd4baa009303), .int 65, .real (Float.ofBits 0x4202a05f20000000)] == "'6'"
#guard printf "% gé%,.*j%+%" [.null, .real (Float.ofBits 0x4059000000000000), .text "12abc", .text "tab\there"] == " 0é12abc%"
#guard printf "é% *.0f%-!0.*Q%-+X" [.text "日本", .text "0x1F", .real (Float.ofBits 0xab2bff2ee48e0530), .text "nl\nx"] == "é 0''0"
#guard printf "%%%!.4g" [.int 1] == "%1.0"
#guard printf "%-!.T" [.real (Float.ofBits 0x0)] == ""
#guard printf "[%- !d]%- 0,.5c" [.blob (ByteArray.mk #[0x41, 0x42]), .int 0, .text ""] == "[ 0]00000"
#guard printf "%!0,llj%114q" [] == "                                                                                                            (NULL)"
#guard printf "%#4.4E" [.null, .real (Float.ofBits 0x1), .null, .text " 12 "] == "0.0000E+00"
#guard printf "%.*E%-q[%zabc%!.o" [] == "0E+00(NULL)[abc0"
#guard printf "x %#!4.7jabc% !0J" [.blob (ByteArray.mk #[])] == "x     abcnull"
#guard printf "x %,*.*j" [.null] == "x "
#guard printf "%-!.f" [] == "0.0"
#guard printf "%+ ,*.10lz%-16.*J" [.real (Float.ofBits 0x0)] == "null            "
#guard printf "%03.x%- #0*.*g" [.int 0, .text " 12 ", .blob (ByteArray.mk #[0xff]), .text "12abc"] == "000 1.e+01     "
#guard printf "%#d" [.real (Float.ofBits 0x1), .blob (ByteArray.mk #[]), .null] == "0"
#guard printf "%,g%#.20Eabc%+ 0.u" [.real (Float.ofBits 0x400921f9f01b866e), .real (Float.ofBits 0xab2bff2ee48e0530), .null] == "3.14159-1.00000000000000000000E-100abc0"
#guard printf "%-#,d - %+ 7.*%% 0.s" [.int 0, .null, .text "x\"y"] == "0 -       %"
#guard pfHex "%!3w% .1c" [.null] == "284e554c4c2900"
#guard printf "%fx %-.4g" [.blob (ByteArray.mk #[0x41]), .null, .text "a%b"] == "0.000000x 0"
#guard printf "]%-+ #3.14q% 0e%#,.17d% ,.g" [] == "](NULL) 0.000000e+0000,000,000,000,000,000 0"
#guard printf "[%!0y" [.blob (ByteArray.mk #[0x41, 0x42])] == "["
#guard printf "%#.e%+ .13c]%!.*j]%,z" [.text "é漢字z", .real (Float.ofBits 0x4058e00000000000), .text "é漢字z"] == "0.e+009999999999999]]"
#guard printf "abc%+.1x" [.int (-3), .int (-42), .int 65, .text "0x1F"] == "abcfffffffffffffffd"
#guard printf "%%%+,5.*z%.f" [.text "é漢字z", .real (Float.ofBits 0x3fe0000000000000)] == "%     0"
#guard printf "é%-+.*i%0.%" [.real (Float.ofBits 0x3fe0000000000000)] == "é+0%"
#guard printf "%- #.J" [.text "abc def", .blob (ByteArray.mk #[0x41]), .int (-1), .real (Float.ofBits 0x0)] == "\"\""
#guard printf "abc% !0q%!.7X%0c%.0x" [.text "3.7e1", .null, .int 255] == "abc3.7e1000000020"
#guard printf "é%-w" [.int 12, .int (-1)] == "é12"
#guard printf "%.20c% .21j%#11.r%+!0,.10s" [.int 9223372036854775807] == "99999999999999999999        0th"
#guard printf "% 0.6r%1d%" [.real (Float.ofBits 0xfe6ddd4baa009303), .text "hello"] == "-9223372036854775808th0%"
#guard pfHex "%+ 0w%-+ !.*c - %-*.6u" [.text "😀x"] == "f09f98807800202d20303030303030"
#guard printf "%+12i%+!11.*X%+ 017d" [.null] == "          +0          0 0000000000000000"
#guard printf "%+.14d" [.null, .blob (ByteArray.mk #[0x41]), .real (Float.ofBits 0x4058e00000000000), .null] == "+00000000000000"
#guard printf "% ,.2p% 0f%!*.ly" [.blob (ByteArray.mk #[0xc3, 0xa9]), .blob (ByteArray.mk #[0xc3, 0xa9])] == "00 0.000000"
#guard printf "% i%-#.12w" [.text " 12 "] == " 12(NULL)"
#guard printf "%%%-!009.*e" [.blob (ByteArray.mk #[0x41, 0x42]), .int 0] == "%0.0e+00  "
#guard printf "%+g%-f%!10G" [] == "+00.000000       0.0"
#guard printf "x %,.*f%.3f% !.*d" [.int 16] == "x 0.00000000000000000.000 0"
#guard printf "[%-#,G% .*g]% 0Q" [.real (Float.ofBits 0x4058e00000000000), .text "\x01ctl", .text "-5", .blob (ByteArray.mk #[0x00])] == "[99.5000-5]''"
#guard printf "]%+!,21.*i%0,.10d" [.text "😀x", .text "abc def", .text " 12 ", .text "-5"] == "]                   +00,000,000,012"
#guard printf "abc%0110.8X%.e" [.text "tab\there", .text "x\"y", .int 1, .int 9223372036854775807] == "abc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000e+00"
#guard printf "% #!0,.*g%#,.3Q%+ 0,.6e" [.blob (ByteArray.mk #[0xc3, 0xa9]), .text "A", .int 3] == " 0.'3' 0.000000e+00"
#guard printf "abc%!.*w]%19.*u%- !Q" [] == "abc]                  0NULL"
#guard printf "%12.5c% #0,.15s%-+0,.0E%,.5c" [.int (-1), .int 8, .text "", .text "0x1F"] == "       -----8+0E+0000000"
#guard printf "%0.wx %-!8X - %-#*.*r" [] == "x 0        - 0th"
#guard printf "x %10f" [] == "x   0.000000"
#guard printf "% 0g%f%-Q" [] == " 00.000000NULL"
#guard printf "x %-,11.5X" [.text "abc def"] == "x 00000      "
#guard printf "x %- #c%%%-lo%!.*z" [.blob (ByteArray.mk #[0xc3, 0xa9]), .real (Float.ofBits 0x3f202e7ef70994dd), .real (Float.ofBits 0xab2bff2ee48e0530)] == "x é%0"
#guard printf "%*.*w" [.int (-1), .null] == " "
#guard printf "%#0,*.*%" [.int (-42), .null, .int 16] == "%                                         "
#guard printf "%%%+#0.14Q[%!.j" [.blob (ByteArray.mk #[0xc3, 0xa9]), .int 9223372036854775807] == "%'é'["
#guard printf "abc%,*.d" [.blob (ByteArray.mk #[0xff]), .real (Float.ofBits 0x4345ee2a2eb5a5c4), .int 5, .int (-3)] == "abc12,345,678,901,234,568"
#guard printf "%+ .19e%!.3g%- 1.g%+.0d" [.int 42, .text "A"] == " 4.2000000000000000000e+010.0 0+0"
#guard printf "abc% #s%- #.*c" [.int 65, .null, .text "-5"] == "abc65-"
#guard printf "]%.0u" [.text "a'b", .text "3.7e1"] == "]0"
#guard printf "%-+,.*X - %- 4.2%" [] == "0 - %   "
#guard printf "%+ .*%% !0,016.5pé%d" [.real (Float.ofBits 0xfe6ddd4baa009303)] == "%0000000000000000é0"
#guard printf "%#g" [.real (Float.ofBits 0x3f202e7ef70994dd), .int 0] == "0.000123456"
#guard printf "%%% 00e%-+#!0,.8X%!,.2J" [.int 20, .null, .text "😀x"] == "% 2.000000e+0100000000\"😀x\""
#guard printf "% !*.*r%-!09%%#0.f" [.int 9223372036854775807, .real (Float.ofBits 0xc004000000000000), .text "a%b"] == " 0th%        0."
#guard printf "[%#!.*u" [.int 0, .int 8, .blob (ByteArray.mk #[0x41]), .text " 12 "] == "[8"
#guard printf "]%+,.x% #.*g" [.int 255, .text "-5", .real (Float.ofBits 0x3fb999999999999a), .int (-1)] == "]ff 0.10000"
#guard printf "%#013q%+i%+ #.*w" [.blob (ByteArray.mk #[0x41, 0x42]), .text "0x1F", .blob (ByteArray.mk #[0xff])] == "           AB+0"
#guard printf "[% ,.0lJ%-+!s%o" [] == "[null0"
#guard printf "%,.10w]%#!0.r%+ !,.c%,.1Q" [.int (-9223372036854775807), .null, .real (Float.ofBits 0x40fe240c9fbe76c9), .int 5] == "-922337203]0th1'5'"
#guard printf "%!G" [] == "0.0"
#guard printf "x %-+!6.7Q%020.21s%0.q%.13s" [.blob (ByteArray.mk #[0xc3, 0xa9]), .real (Float.ofBits 0x3fe0000000000000), .real (Float.ofBits 0x54b249ad2594c37d), .text "tab\there"] == "x 'é'                    0.5tab\there"
#guard printf "%%%0p%-*.8n% !9G" [.int 255, .int 3, .int 9223372036854775807, .text "back\\slash"] == "%FF 9.22337E+18"
#guard printf "%-+006.e" [.text "0x1F", .real (Float.ofBits 0x3f202e7ef70994dd), .int (-3)] == "+0e+00"
#guard printf "%-11.l% - %#!n%#u" [.blob (ByteArray.mk #[0x41]), .blob (ByteArray.mk #[0xff])] == "%           - 0"
#guard printf "%-+ #21z%%%#!.*g%" [] == "                     %0.%"
#guard printf "%+ .14Qé%!,.20%%.*c" [.int 12, .real (Float.ofBits 0xc004000000000000), .int (-42)] == "'12'é%--"
#guard printf "%x" [.int 42] == "2a"
#guard printf "%%% #0.8c[%-.12%x %-14.X%+,*.z" [.int 1, .text "a'b", .int (-42), .real (Float.ofBits 0x4321c37937e08000)] == "%11111111[%x 0                                                       "
#guard printf "]%+Ex %d" [.real (Float.ofBits 0x4058e00000000000), .text " 12 ", .text "0x1F"] == "]+9.950000E+01x 12"
#guard printf "%-+0,.17d%#!q% .*d" [.real (Float.ofBits 0x3fe0000000000000), .blob (ByteArray.mk #[])] == "+00,000,000,000,000,000 0"
#guard printf "é%,s%!.*lX%+*p" [.blob (ByteArray.mk #[0x41, 0x42]), .blob (ByteArray.mk #[0xc3, 0xa9])] == "éAB00"
#guard printf "%+,j%#y[%- #!,*.*u" [.text "hello", .int 9223372036854775807] == "hello"
#guard printf "%.x" [.real (Float.ofBits 0x3fe0000000000000)] == "0"
#guard printf "%#Q" [] == "NULL"
#guard printf "%.*s% ,.10g" [.real (Float.ofBits 0x3fe0000000000000), .text "nl\nx"] == " 0"
#guard printf "%-0.c%+021.17e%#*X%- .*f" [.real (Float.ofBits 0x1), .int (-1), .text "é漢字z"] == "4-1.00000000000000000e+000 0"
#guard pfHex "%-+ #*c" [.text "back\\slash"] == "00"
#guard printf "%g" [.text "3.7e1", .text "12abc", .int (-1)] == "37"
#guard printf "%#!.Q" [.text "nl\nx", .null] == "''"
#guard printf "%!s%+ 113.1g]% !0i" [.null, .null, .int (-1), .null] == "                                                                                                                0]-1"
#guard printf "%!1.*f" [.int (-9223372036854775807), .null, .blob (ByteArray.mk #[]), .null] == "0.0"
#guard printf "x %5.llE%6G%" [] == "x 0E+00     0%"
#guard printf "%2.3y%-s%-02x" [] == ""
#guard printf "x %-.*s" [.blob (ByteArray.mk #[]), .int 12, .real (Float.ofBits 0x4202a05f20000000)] == "x "
#guard printf "% !J%+!.6o%+04.20q" [.real (Float.ofBits 0x54b249ad2594c37d), .text "12abc", .real (Float.ofBits 0x3f202e7ef70994dd), .blob (ByteArray.mk #[])] == "\"1.0e+100\"0000140.000123456"
#guard printf "%-#.*dx %*n" [.text "tab\there", .int 1] == "1x "
#guard printf "% #!0*i[%.2f" [.int 8, .text "nl\nx"] == " 0000000[0.00"
#guard printf "%x%!11.*llg% ,.*lJ" [.int (-3), .real (Float.ofBits 0x400921f9f01b866e), .text "日本", .text "0x1F"] == "fffffffffffffffd        0.0null"
#guard pfHex "%#,.s%!*.*c" [] == "00"
#guard printf "%-0.2s" [.text "x\"y", .int 0] == "x\""
#guard printf " - %,.3Xx %#0,*j[%#!0.0s" [.int 3, .blob (ByteArray.mk #[0x41])] == " - 003x ["
#guard printf "%+01.9f" [.real (Float.ofBits 0x3fb999999999999a), .int 9223372036854775807] == "+0.100000000"
#guard printf "é%!e - %-.1u" [.real (Float.ofBits 0x400921f9f01b866e)] == "é3.14159e+00 - 0"
#guard printf "%-+4.p%+0*z" [.int 12, .blob (ByteArray.mk #[0xff]), .text "-5", .text "日本"] == "C   -5"
#guard printf "]% .*X" [.text "back\\slash", .real (Float.ofBits 0x3e8421f5f40d8376)] == "]0"
#guard pfHex "%*.10Eé%-#!*c" [.real (Float.ofBits 0x3fe0000000000000)] == "302e30303030303030303030452b3030c3a900"
#guard printf "%,*.Q% J%%% .4Q" [.null, .blob (ByteArray.mk #[0x41, 0x42]), .blob (ByteArray.mk #[0xc3, 0xa9])] == "''\"é\"%NULL"
#guard printf "%#,3g" [.int 8, .text "3.7e1", .int 5] == "8.00000"
#guard printf "%%%0*f" [] == "%0.000000"
#guard printf "% X% ld%#,*.10G" [.real (Float.ofBits 0xfe6ddd4baa009303), .null] == "8000000000000000 00.000000000"
#guard printf "%!023.e%!li" [.int 3, .blob (ByteArray.mk #[0x41])] == "00000000000000003.0e+000"
#guard printf "%-,8.*Q% !f%+#0.13Q%+ !.15p" [.int (-1), .int (-42), .real (Float.ofBits 0x4059000000000000)] == "'-'      100.0NULL000000000000000"
#guard printf "abc% 4.*j" [.real (Float.ofBits 0x7e6ddd4baa009303)] == "abc    "
#guard printf "%#!12.z%.*f" [] == "            0"
#guard printf "%+1.17g%,d%-+,w%+r" [.blob (ByteArray.mk #[0x41, 0x42]), .blob (ByteArray.mk #[0xff]), .real (Float.ofBits 0xfe6ddd4baa009303)] == "+00-1.0e+301+0th"
#guard printf "%-llw%-+0.*g%+ 19.lls" [] == "(NULL)+0                   "
#guard printf "%#.*u" [] == "0"
#guard printf "%8o% n" [] == "       0"
#guard printf "%!ld%,j%+ *.9%" [] == "0%"
#guard printf "[%4.*o" [.blob (ByteArray.mk #[])] == "[   0"
#guard pfHex "é%-+0*.*c]%+05.j" [] == "c3a9005d2020202020"
#guard printf "%+0.6x%1.*p" [.text "9999999999999999999", .text "", .int (-3), .int 12] == "7fffffffffffffffFFFFFFFFFFFFFFFD"
#guard printf "%-7.13f" [.int (-1)] == "-1.0000000000000"
#guard printf "% #.*X%+.17i" [.int (-3), .real (Float.ofBits 0x3f202e7ef70994dd), .real (Float.ofBits 0x4058e00000000000)] == "000+00000000000000099"
#guard printf "abc% ,.8w" [.int (-1), .real (Float.ofBits 0xc004000000000000)] == "abc-1"
#guard printf "% 1.*f% #.16f" [.null, .text "-5", .real (Float.ofBits 0xab2bff2ee48e0530), .real (Float.ofBits 0x3e8421f5f40d8376)] == "-5-0.0000000000000000"
#guard pfHex "]%!c%.*i%-!19lw" [] == "5d0030284e554c4c2920202020202020202020202020"
#guard printf "abc%0fabc%!.ux %0.d%" [] == "abc0.000000abc0x 0%"
#guard printf "%-#.f%0.*f%%% #*.*f" [.text "nl\nx", .real (Float.ofBits 0x401c000000000000), .int 9223372036854775807, .null] == "0.9223372036854776000.0000000% 0."
#guard printf "%#022s" [.real (Float.ofBits 0x4058e00000000000), .blob (ByteArray.mk #[]), .int 20, .null] == "                  99.5"
#guard printf "%!,.13lz" [.blob (ByteArray.mk #[0xc3, 0xa9]), .blob (ByteArray.mk #[0x00]), .blob (ByteArray.mk #[0xff]), .text "😀x"] == "é"
#guard printf "%12.Q" [.blob (ByteArray.mk #[0x41, 0x42]), .text "a%b", .text ""] == "          ''"
#guard printf "%#*.7J]%.*lX%" [.real (Float.ofBits 0xc004000000000000), .text "0x1F", .int 42, .text "hello"] == "\"0x1F\"]000000000000000000000000000000000000000000%"
#guard printf "%+#!.*g%-#.0eabc%- .j%*.*x" [.blob (ByteArray.mk #[0x00])] == "+0.0.e+00abc0"
#guard printf "%+0*.*w%*s" [.text "tab\there", .null, .blob (ByteArray.mk #[])] == ""
#guard printf "%+j[%-+#,26.x%0.2u" [.real (Float.ofBits 0xab2bff2ee48e0530), .null] == "-1.0e-100[0                         00"
#guard printf "% !.u%118q" [] == "0                                                                                                                (NULL)"
#guard printf "]% .u%+#.j%014s" [.int (-42), .real (Float.ofBits 0x1), .text "😀x"] == "]18446744073709551574         😀x"
#guard printf "]%.11jx %,*.8g%+!,014s" [] == "]x 0              "
#guard printf "%#!.7q%!8.Té%-+#.8T" [.blob (ByteArray.mk #[0xc3, 0xa9])] == "é"
#guard printf "%.*%%-113.z" [] == "%                                                                                                                 "
#guard printf "]% %%-+17.o" [] == "]%0                "
#guard printf "%+0.*c" [.text "a%b", .real (Float.ofBits 0x0), .text "a%b", .blob (ByteArray.mk #[0x00])] == "0"
#guard printf "%.1w[% 8G" [.null] == "([       0"
#guard pfHex "%3.9c%.4s]%!0.14c% .14r" [.int 255, .int 3] == "323232323232323232335d0000000000000000000000000000203030303030303030303030307468"
#guard printf "% .G%-+x" [.int 12, .real (Float.ofBits 0x1), .text "abc def", .real (Float.ofBits 0x7e6ddd4baa009303)] == " 1E+010"
#guard printf "%-*w%0%%- 0z" [.text "a'b", .real (Float.ofBits 0x400921f9f01b866e), .real (Float.ofBits 0x3fe0000000000000)] == "3.14159%0.5"
#guard printf "%%%+.1x%#06dx %q%" [.null, .text "12abc", .int 0, .text "a%b"] == "%0000012x 0%"
#guard printf "é%*.20q%+#0.*%" [.int 5] == "é(NULL)%"
#guard printf "%0.8f%*.*x%%%#.1o" [.blob (ByteArray.mk #[0xff]), .null, .blob (ByteArray.mk #[0xff]), .blob (ByteArray.mk #[])] == "0.000000000%0"
#guard printf "% 9.9n%1x" [.real (Float.ofBits 0xab2bff2ee48e0530), .real (Float.ofBits 0xc004000000000000), .int (-42), .null] == "0"
#guard printf "%%%-+0,.16z%+#,.*f" [.int 8, .text "tab\there", .int 0, .real (Float.ofBits 0x3fe0000000000000)] == "%8+0."
#guard printf " - %!,.g" [.int 16, .blob (ByteArray.mk #[0xc3, 0xa9]), .text "3.7e1"] == " - 2.0e+01"
#guard printf "%-019.*jx %-+#*f" [.real (Float.ofBits 0x4321c37937e08000)] == "                   x +0.000000"
#guard pfHex "%+,.*s%+#2q%%% 0.17c]%- ,.14e" [.blob (ByteArray.mk #[])] == "284e554c4c292500000000000000000000000000000000005d20302e3030303030303030303030303030652b3030"
#guard printf "%+ fx %+,s%%" [.null] == " 0.000000x %"
#guard printf "%+!.12eé%- !.*g" [.text "-5", .null] == "-5.0e+00é 0.0"
#guard printf "%+.4z" [] == ""
#guard printf "%!*.d" [.int 16, .null, .int (-9223372036854775807)] == "               0"
#guard pfHex "abc%+ !,*z" [.int 3, .blob (ByteArray.mk #[0xff]), .real (Float.ofBits 0x3f202e7ef70994dd)] == "6162632020ff"
#guard printf "%%%-+!.5z%!0.13z" [] == "%"
#guard printf "%-#n%" [.text "\x01ctl"] == "%"
#guard printf "% #!r%+#!,1.d%#!0,%%-0.10x" [] == " 0th+0%0000000000"
#guard printf "[%0,9.0w%06.*s" [] == "[               "
#guard printf " - %0.5q" [.int 5, .int 1] == " - 5"
#guard printf "[%!022.4s%-021.g%*.17E" [] == "[                      0                    0.00000000000000000E+00"
#guard printf "%-+ *.4%é% #d%#!e% 12.x" [.int (-1), .null, .blob (ByteArray.mk #[0x41])] == "%é 00.0e+00           0"
#guard printf "%+09w" [.text "3.7e1"] == "    3.7e1"
#guard pfHex "%+0.11s - %!24.17r" [.blob (ByteArray.mk #[0xff]), .real (Float.ofBits 0x1)] == "ff202d20202020202020203030303030303030303030303030307468"
#guard printf "%18u" [.null, .int 42, .null, .real (Float.ofBits 0x400921f9f01b866e)] == "                 0"
#guard printf "%-,.*q%0.u" [.blob (ByteArray.mk #[0x41])] == "0"
#guard printf "%-04llw]%#!,210y" [] == "(NULL)]"
#guard printf "%-+x" [.real (Float.ofBits 0x3f202e7ef70994dd), .null, .real (Float.ofBits 0xfe6ddd4baa009303)] == "0"
#guard printf "% !.8f" [.real (Float.ofBits 0x40fe240c9fbe76c9), .blob (ByteArray.mk #[0xc3, 0xa9]), .real (Float.ofBits 0xfe6ddd4baa009303)] == " 123456.789"
#guard pfHex "%+#12.9%%!0.18s%!0.0c" [.int (-1)] == "2020202020202020202020252d3100"
#guard printf " - %#,q" [.int (-1), .text "", .int (-9223372036854775807)] == " - -1"
#guard printf "%-#,G%#g%!0*.10x%!*.f" [.text "\x01ctl", .int 12] == "0.0000012.000000000000000.0"
#guard printf "é% .17dabc% 2.18iabc%+0024.*e" [.int 0] == "é 00000000000000000abc 000000000000000000abc+0000000000000000000e+00"
#guard printf "]% #.4J" [.text "\x01ctl", .real (Float.ofBits 0x3f202e7ef70994dd)] == "]\"\\u0001ctl\""
#guard printf "abc%!*.*Jé%25.r%-+#!014d" [.null] == "abcnullé                      0th+0000000000000"
#guard printf "%0013p%0,26e" [] == "0000000000000000000000000000.000000e+00"
#guard printf "%#.*X%*G%- ,8.4e[%!*.17o" [.text "0x1F", .int 65, .blob (ByteArray.mk #[0x00]), .int (-9223372036854775807)] == "0X41-9.22337E+18 0.0000e+00[00000000000000000"
#guard printf "% 11.13ex %-+ .zx % #!,10.17f" [] == " 0.0000000000000e+00x x        0.0"
#guard printf "% 017lgé%*.n" [.text "hello", .real (Float.ofBits 0x3f202e7ef70994dd), .int 65, .int 65] == " 0000000000000000é"
#guard printf "%-+ ,z%" [.blob (ByteArray.mk #[0x41])] == "A%"
#guard printf "%-+016.q%0,.9s% 5.*p%-+.16w" [.text "hello", .int 0, .null] == "                0    0(NULL)"
#guard printf "%+020.*g" [.int 20, .null, .int 8, .blob (ByteArray.mk #[0x41])] == "+0000000000000000000"
#guard printf "]%#.1sé%-e" [.blob (ByteArray.mk #[0x41]), .text " 12 ", .real (Float.ofBits 0x3f202e7ef70994dd), .real (Float.ofBits 0x3fe0000000000000)] == "]Aé1.200000e+01"
#guard pfHex "]%#!0,.9u%0.*c" [] == "5d3030302c3030302c30303000"
#guard printf "%.z" [.text "hello"] == ""
#guard printf "%+0,6i% !,.9g" [.real (Float.ofBits 0x3fe0000000000000), .int 255, .int 65] == "+00,000 255.0"
#guard printf "%+!xé%7c%.2g%" [.null, .real (Float.ofBits 0x4321c37937e08000), .text "\x01ctl", .int (-9223372036854775807)] == "0é      20%"
#guard printf "[%!02.4q" [.real (Float.ofBits 0x40fe240c9fbe76c9), .int 3, .text "12abc", .text "😀x"] == "[1234"
#guard printf "[%#0y%,r" [.int 12, .null, .text "x\"y", .null] == "["
#guard printf "%117.11f% 2G" [.int 0] == "                                                                                                        0.00000000000 0"
#guard printf "]%- !.x" [.int 42, .text ""] == "]2a"
#guard printf "%!1ly]%-#,E%" [.real (Float.ofBits 0x401c000000000000), .real (Float.ofBits 0x3fe0000000000000)] == ""
#guard printf "% 12.*q" [.int 5] == "       (NULL"
#guard printf "%- .*r" [.null] == " 0th"
#guard printf "%%%!.*J" [.int 1, .text " 12 ", .int 255, .real (Float.ofBits 0x0)] == "%\" \""
#guard printf "%!*.*Xx %+0.6Gx % .13jx %+*d" [.real (Float.ofBits 0x54b249ad2594c37d), .int 65] == "00000000000000000000000000000000000000000000000000000000000000000x +0x x +0"
#guard printf "%-.*r" [.real (Float.ofBits 0x3e8421f5f40d8376)] == "0th"
#guard printf "%.*dé%-!.5g%e" [.real (Float.ofBits 0x3f202e7ef70994dd), .null] == "0é0.00.000000e+00"
#guard printf " - %-+.*x" [] == " - 0"
#guard printf "[%!9.*i - %11.*ly%-f" [] == "[        0 - "
#guard printf "%-+0119u" [.real (Float.ofBits 0x7e6ddd4baa009303), .real (Float.ofBits 0x4058e00000000000), .text "A"] == "00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000009223372036854775807"
#guard printf "abc% !0.16s" [.null, .text "tab\there"] == "abc"
#guard printf "]%+#01ix %.*s" [.int 5, .int (-1)] == "]+5x "
#guard pfHex "%+ #.*d[%#!*q%#.pé%-+,.c" [.null, .text "hello", .real (Float.ofBits 0x4058e00000000000), .blob (ByteArray.mk #[0xc3, 0xa9])] == "20305b2020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020202020c3a930c3a900"
#guard printf "%012.lué%#20q%.8q" [.text "é漢字z", .int 42, .real (Float.ofBits 0x0), .text "0x1F"] == "000000000000é                  420.0"
#guard printf "%-.5u%!.0j" [.null, .int (-1), .null, .text "back\\slash"] == "00000"
#guard printf "é%-+0*.7d" [.real (Float.ofBits 0x3ee4f8b588e368f1)] == "é+0000000"
#guard printf "% *.11u%08yx %.10e" [.null, .int (-1)] == "18446744073709551615"
#guard printf "%-#,010.21d" [.real (Float.ofBits 0x3ee4f8b588e368f1)] == "000,000,000,000,000,000,000"
#guard printf "%#s%x" [] == "0"
#guard printf "% !5.20X" [.blob (ByteArray.mk #[0xff]), .blob (ByteArray.mk #[0xc3, 0xa9]), .real (Float.ofBits 0x1)] == "00000000000000000000"
#guard printf "%+08.s%-+,n%+.z" [] == "        "
#guard printf "%%%-+10.*g%" [.blob (ByteArray.mk #[0x41, 0x42]), .int 42, .real (Float.ofBits 0x4059000000000000), .blob (ByteArray.mk #[0x41])] == "%+4e+01    %"
#guard pfHex "x %+,4.1s]%3llo" [.text "😀x", .real (Float.ofBits 0x400921f9f01b866e), .int 5, .blob (ByteArray.mk #[0xff])] == "7820202020f05d202033"
#guard printf "%#,13n%" [.blob (ByteArray.mk #[0xff]), .real (Float.ofBits 0x1), .real (Float.ofBits 0x3f202e7ef70994dd)] == "%"
#guard printf "%11X%+.2E" [] == "          0+0.00E+00"
#guard printf "%#0c" [.real (Float.ofBits 0x4059000000000000), .real (Float.ofBits 0xc004000000000000), .null, .real (Float.ofBits 0x0)] == "1"
#guard printf "é%.c" [.int 3, .real (Float.ofBits 0x40fe240c9fbe76c9), .int 16] == "é3"
#guard printf "%3.*G" [] == "  0"
#guard printf "abc%+!0.*llr]%,7q" [] == "abc+0th] (NULL)"
#guard printf "%,.*p" [.int 65, .null, .text "tab\there", .null] == "00000000000000000000000000000000000000000000000000000000000000000"
#guard printf "%.u" [.int 9223372036854775807, .blob (ByteArray.mk #[0x41]), .real (Float.ofBits 0x4202a05f20000000), .int 3] == "9223372036854775807"
#guard printf "%-+!.f%-+1s%-+#!,u%*.X" [.text "-5", .int 16, .int 9223372036854775807, .null] == "-5.0169,223,372,036,854,775,8070"
#guard printf "%.i%+f]%-+!0,3.0e" [.text "hello"] == "0+0.000000]+0.0e+00"
#guard printf "[%0x - %lg" [.null, .real (Float.ofBits 0x1), .blob (ByteArray.mk #[0x41, 0x42])] == "[0 - 4.94066e-324"
#guard printf "%+.20c" [.int 0, .int 255] == "00000000000000000000"
#guard printf "%-!.q%025Q]%-n" [.real (Float.ofBits 0x3fb999999999999a)] == "                     NULL]"
#guard pfHex " - %,c" [.blob (ByteArray.mk #[0x00]), .text "日本", .real (Float.ofBits 0x3f202e7ef70994dd), .text "日本"] == "202d2000"
#guard printf " - %+ 4.*s%- 0.*s" [.int 16, .text "3.7e1"] == " - 3.7e1"
#guard printf "%!X" [.blob (ByteArray.mk #[0x41]), .text "-5"] == "0"
#guard printf " - %-z[%.15rx % !,.*u" [.null, .int 1, .text "\x01ctl"] == " - [0000000000001stx 0"
#guard printf "%#0s%-.8f" [.blob (ByteArray.mk #[0xc3, 0xa9]), .real (Float.ofBits 0x3ee4f8b588e368f1), .int (-42), .real (Float.ofBits 0x3fb999999999999a)] == "é0.00001000"
#guard printf "% !,18.19G" [.blob (ByteArray.mk #[0x41, 0x42]), .null] == "               0.0"
#guard printf "%-#13.*X%-f%-+ 013.*X%.E" [.null, .text "é漢字z", .text "tab\there"] == "0            0.00000000000000000000E+00"
#guard printf "é%+ !.0r" [.int 16, .real (Float.ofBits 0x400921f9f01b866e), .int (-42)] == "é 16th"
#guard printf "%.g - %8.j" [.text "9999999999999999999", .int 16] == "1e+19 -         "
#guard printf "%!0.13g%+#.pabc%#,20g%+18e" [.int (-3), .blob (ByteArray.mk #[0x41]), .real (Float.ofBits 0x400921f9f01b866e)] == "-3.00abc             3.14159     +0.000000e+00"
#guard printf "% .*%%11d%9.*r" [.null, .null, .int 16, .null] == "%          000000000000000th"
#guard printf "%-!s%+ ,.f%#03.10E%-#*.14j" [.null, .int (-9223372036854775807)] == "-9,223,372,036,854,776,0000.0000000000E+00"
#guard printf "%04w%%%*%" [.text ""] == "    %%"
#guard printf "%0*.7G%+#*.8q%+018.0f" [.int 8, .null, .real (Float.ofBits 0x1), .real (Float.ofBits 0x4321c37937e08000)] == "0000000025000000+00000000000000000"
#guard printf "%+!,w%-+.16o%#g%Q" [.null] == "(NULL)00000000000000000.00000NULL"
#guard printf "%-0j]%13.j%%%-+,u" [.int 65] == "65]             %0"
#guard printf "%+0.17jé%+#11.*%" [.real (Float.ofBits 0x401c000000000000)] == "7.0é          %"
#guard printf "%+.*f%#,10ld" [.null, .real (Float.ofBits 0x4202a05f20000000), .real (Float.ofBits 0x4345ee2a2eb5a5c4), .blob (ByteArray.mk #[])] == "+1000000000012,345,678,901,234,568"
#guard printf "%- #!.g%0*.p" [.null, .text "tab\there", .real (Float.ofBits 0x4321c37937e08000), .int (-1)] == " 0.8E1BC9BF04000"
#guard printf "%%%+0J%-#!x%- .s" [.null] == "%null0"
#guard printf "]%6.*f" [.real (Float.ofBits 0xab2bff2ee48e0530), .int (-9223372036854775807), .text "9999999999999999999"] == "]-9223372036854776000"
#guard printf "%o%!0,o%!1.*X%" [.blob (ByteArray.mk #[0x00]), .real (Float.ofBits 0x4059000000000000)] == "01440%"
#guard printf "%- .4o" [.real (Float.ofBits 0x0), .text " 12 ", .int 42] == "0000"
#guard printf "% 1.*d" [.real (Float.ofBits 0x400921f9f01b866e)] == " 000"
#guard printf "abc%- #,.8o%#012X" [.real (Float.ofBits 0xab2bff2ee48e0530), .text "é漢字z", .int 9223372036854775807, .blob (ByteArray.mk #[0xc3, 0xa9])] == "abc00000000000000000000"
#guard printf "x %#!*J% 0.*llg" [.text "A"] == "x null 0"
#guard printf "%+,8s" [.int 16, .text "😀x"] == "      16"
#guard printf "% #9p%+.*G%" [.real (Float.ofBits 0xab2bff2ee48e0530), .real (Float.ofBits 0x1), .text "hello"] == "        0+0%"
#guard printf "%*.X%- .1G" [.blob (ByteArray.mk #[])] == "0 0"
#guard printf "]%+.*i%+#,017p" [.real (Float.ofBits 0x400921f9f01b866e), .text "日本"] == "]+00000000000000000000"
#guard printf "%.2j%-+ .8s" [] == ""
#guard printf "[%- 011.lln%px %d" [] == "[0x 0"
#guard printf "[% 1.*p%3.e[%,7.17f%-+00.*r" [.text "12abc", .text "a%b", .blob (ByteArray.mk #[0x00])] == "[0000000000000e+00[0.00000000000000000+0th"
#guard printf "]%#!0q" [.text "nl\nx", .real (Float.ofBits 0x3ee4f8b588e368f1), .text "hello", .int 16] == "]nl\\u000ax"
#guard printf "%#!x%.d%+.*g" [.null] == "00+0"

/-! ### Corner cases found while comparing against sqlite 3.54 -/
-- round keeps the sign of zero for n > 0 but not for n = 0
#guard (roundReal (-0.04) 1).toBits == 0x8000000000000000
#guard (roundReal (-0.004) 2).toBits == 0x8000000000000000
#guard (roundReal (-0.4) 0).toBits == 0
#guard (roundReal 0.49999999999999994 0) == 1.0
-- a huge float precision is clamped, not an error
#guard printf "%.2000000000g" [.real 1.5] == "1.5"
-- embedded NUL: AtoF stops there (value 12.0), Atoi64 and the numeric affinity read the whole text
#guard (atoFBytes (ByteArray.mk #[0x31, 0x32, 0x00, 0x33, 0x34])).value == 12.0
#guard showV (castToNumeric (.blob (ByteArray.mk #[0x31, 0x32, 0x00, 0x33]))) == "integer:12"
#guard showV (numericValue (.blob (ByteArray.mk #[0x31, 0x32, 0x00, 0x33]))) == "real:12.0"
#guard castToInt (.blob (ByteArray.mk #[0x31, 0x32, 0x00, 0x33])) == 12
-- the INTEGER-affinity examples of the task
#guard numStr "1e2" == "integer:100"
#guard numStr "3.0" == "integer:3"
#guard numStr "3.5" == "real:3.5"
#guard numStr " 7 " == "integer:7"
#guard numStr "0x10" == "text:0x10"
#guard numStr "9223372036854775808" == "real:9.2233720368547758e+18"
