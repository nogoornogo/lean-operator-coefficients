import Math.Algebra.HiggsFourWaveCubature.Structural.CollinearData

/-! Exact node transports for the unchanged 288-point transverse family. -/
namespace Math.HiggsFourWaveCubature.Structural.Transverse
set_option autoImplicit false

def euclid (a : Fin 288) (s i : Fin 4) : GaussianInt := wick i*raw 0 a s i


def swap01Index (a : Fin 288) : Fin 288 :=
  if a.val < 144 then
    if a.val < 72 then
      if a.val < 36 then
        if a.val < 18 then
          if a.val < 9 then
            if a.val < 4 then
              if a.val < 2 then
                if a.val < 1 then
                  47
                else
                  46
              else
                if a.val < 3 then
                  45
                else
                  44
            else
              if a.val < 6 then
                if a.val < 5 then
                  40
                else
                  41
              else
                if a.val < 7 then
                  42
                else
                  if a.val < 8 then
                    43
                  else
                    243
          else
            if a.val < 13 then
              if a.val < 11 then
                if a.val < 10 then
                  241
                else
                  242
              else
                if a.val < 12 then
                  240
                else
                  247
            else
              if a.val < 15 then
                if a.val < 14 then
                  246
                else
                  245
              else
                if a.val < 16 then
                  244
                else
                  if a.val < 17 then
                    251
                  else
                    249
        else
          if a.val < 27 then
            if a.val < 22 then
              if a.val < 20 then
                if a.val < 19 then
                  250
                else
                  248
              else
                if a.val < 21 then
                  255
                else
                  254
            else
              if a.val < 24 then
                if a.val < 23 then
                  253
                else
                  252
              else
                if a.val < 25 then
                  259
                else
                  if a.val < 26 then
                    257
                  else
                    258
          else
            if a.val < 31 then
              if a.val < 29 then
                if a.val < 28 then
                  256
                else
                  263
              else
                if a.val < 30 then
                  262
                else
                  261
            else
              if a.val < 33 then
                if a.val < 32 then
                  260
                else
                  267
              else
                if a.val < 34 then
                  265
                else
                  if a.val < 35 then
                    266
                  else
                    264
      else
        if a.val < 54 then
          if a.val < 45 then
            if a.val < 40 then
              if a.val < 38 then
                if a.val < 37 then
                  271
                else
                  270
              else
                if a.val < 39 then
                  269
                else
                  268
            else
              if a.val < 42 then
                if a.val < 41 then
                  4
                else
                  5
              else
                if a.val < 43 then
                  6
                else
                  if a.val < 44 then
                    7
                  else
                    3
          else
            if a.val < 49 then
              if a.val < 47 then
                if a.val < 46 then
                  2
                else
                  1
              else
                if a.val < 48 then
                  0
                else
                  205
            else
              if a.val < 51 then
                if a.val < 50 then
                  207
                else
                  204
              else
                if a.val < 52 then
                  206
                else
                  if a.val < 53 then
                    201
                  else
                    203
        else
          if a.val < 63 then
            if a.val < 58 then
              if a.val < 56 then
                if a.val < 55 then
                  200
                else
                  202
              else
                if a.val < 57 then
                  197
                else
                  199
            else
              if a.val < 60 then
                if a.val < 59 then
                  196
                else
                  198
              else
                if a.val < 61 then
                  193
                else
                  if a.val < 62 then
                    195
                  else
                    192
          else
            if a.val < 67 then
              if a.val < 65 then
                if a.val < 64 then
                  194
                else
                  229
              else
                if a.val < 66 then
                  231
                else
                  228
            else
              if a.val < 69 then
                if a.val < 68 then
                  230
                else
                  225
              else
                if a.val < 70 then
                  227
                else
                  if a.val < 71 then
                    224
                  else
                    226
    else
      if a.val < 108 then
        if a.val < 90 then
          if a.val < 81 then
            if a.val < 76 then
              if a.val < 74 then
                if a.val < 73 then
                  237
                else
                  239
              else
                if a.val < 75 then
                  236
                else
                  238
            else
              if a.val < 78 then
                if a.val < 77 then
                  233
                else
                  235
              else
                if a.val < 79 then
                  232
                else
                  if a.val < 80 then
                    234
                  else
                    181
          else
            if a.val < 85 then
              if a.val < 83 then
                if a.val < 82 then
                  183
                else
                  180
              else
                if a.val < 84 then
                  182
                else
                  177
            else
              if a.val < 87 then
                if a.val < 86 then
                  179
                else
                  176
              else
                if a.val < 88 then
                  178
                else
                  if a.val < 89 then
                    189
                  else
                    191
        else
          if a.val < 99 then
            if a.val < 94 then
              if a.val < 92 then
                if a.val < 91 then
                  188
                else
                  190
              else
                if a.val < 93 then
                  185
                else
                  187
            else
              if a.val < 96 then
                if a.val < 95 then
                  184
                else
                  186
              else
                if a.val < 97 then
                  221
                else
                  if a.val < 98 then
                    223
                  else
                    220
          else
            if a.val < 103 then
              if a.val < 101 then
                if a.val < 100 then
                  222
                else
                  217
              else
                if a.val < 102 then
                  219
                else
                  216
            else
              if a.val < 105 then
                if a.val < 104 then
                  218
                else
                  213
              else
                if a.val < 106 then
                  215
                else
                  if a.val < 107 then
                    212
                  else
                    214
      else
        if a.val < 126 then
          if a.val < 117 then
            if a.val < 112 then
              if a.val < 110 then
                if a.val < 109 then
                  209
                else
                  211
              else
                if a.val < 111 then
                  208
                else
                  210
            else
              if a.val < 114 then
                if a.val < 113 then
                  114
                else
                  115
              else
                if a.val < 115 then
                  112
                else
                  if a.val < 116 then
                    113
                  else
                    118
          else
            if a.val < 121 then
              if a.val < 119 then
                if a.val < 118 then
                  119
                else
                  116
              else
                if a.val < 120 then
                  117
                else
                  122
            else
              if a.val < 123 then
                if a.val < 122 then
                  123
                else
                  120
              else
                if a.val < 124 then
                  121
                else
                  if a.val < 125 then
                    126
                  else
                    127
        else
          if a.val < 135 then
            if a.val < 130 then
              if a.val < 128 then
                if a.val < 127 then
                  124
                else
                  125
              else
                if a.val < 129 then
                  130
                else
                  131
            else
              if a.val < 132 then
                if a.val < 131 then
                  128
                else
                  129
              else
                if a.val < 133 then
                  134
                else
                  if a.val < 134 then
                    135
                  else
                    132
          else
            if a.val < 139 then
              if a.val < 137 then
                if a.val < 136 then
                  133
                else
                  138
              else
                if a.val < 138 then
                  139
                else
                  136
            else
              if a.val < 141 then
                if a.val < 140 then
                  137
                else
                  142
              else
                if a.val < 142 then
                  143
                else
                  if a.val < 143 then
                    140
                  else
                    141
  else
    if a.val < 216 then
      if a.val < 180 then
        if a.val < 162 then
          if a.val < 153 then
            if a.val < 148 then
              if a.val < 146 then
                if a.val < 145 then
                  171
                else
                  170
              else
                if a.val < 147 then
                  169
                else
                  168
            else
              if a.val < 150 then
                if a.val < 149 then
                  175
                else
                  174
              else
                if a.val < 151 then
                  173
                else
                  if a.val < 152 then
                    172
                  else
                    163
          else
            if a.val < 157 then
              if a.val < 155 then
                if a.val < 154 then
                  162
                else
                  161
              else
                if a.val < 156 then
                  160
                else
                  167
            else
              if a.val < 159 then
                if a.val < 158 then
                  166
                else
                  165
              else
                if a.val < 160 then
                  164
                else
                  if a.val < 161 then
                    155
                  else
                    154
        else
          if a.val < 171 then
            if a.val < 166 then
              if a.val < 164 then
                if a.val < 163 then
                  153
                else
                  152
              else
                if a.val < 165 then
                  159
                else
                  158
            else
              if a.val < 168 then
                if a.val < 167 then
                  157
                else
                  156
              else
                if a.val < 169 then
                  147
                else
                  if a.val < 170 then
                    146
                  else
                    145
          else
            if a.val < 175 then
              if a.val < 173 then
                if a.val < 172 then
                  144
                else
                  151
              else
                if a.val < 174 then
                  150
                else
                  149
            else
              if a.val < 177 then
                if a.val < 176 then
                  148
                else
                  86
              else
                if a.val < 178 then
                  84
                else
                  if a.val < 179 then
                    87
                  else
                    85
      else
        if a.val < 198 then
          if a.val < 189 then
            if a.val < 184 then
              if a.val < 182 then
                if a.val < 181 then
                  82
                else
                  80
              else
                if a.val < 183 then
                  83
                else
                  81
            else
              if a.val < 186 then
                if a.val < 185 then
                  94
                else
                  92
              else
                if a.val < 187 then
                  95
                else
                  if a.val < 188 then
                    93
                  else
                    90
          else
            if a.val < 193 then
              if a.val < 191 then
                if a.val < 190 then
                  88
                else
                  91
              else
                if a.val < 192 then
                  89
                else
                  62
            else
              if a.val < 195 then
                if a.val < 194 then
                  60
                else
                  63
              else
                if a.val < 196 then
                  61
                else
                  if a.val < 197 then
                    58
                  else
                    56
        else
          if a.val < 207 then
            if a.val < 202 then
              if a.val < 200 then
                if a.val < 199 then
                  59
                else
                  57
              else
                if a.val < 201 then
                  54
                else
                  52
            else
              if a.val < 204 then
                if a.val < 203 then
                  55
                else
                  53
              else
                if a.val < 205 then
                  50
                else
                  if a.val < 206 then
                    48
                  else
                    51
          else
            if a.val < 211 then
              if a.val < 209 then
                if a.val < 208 then
                  49
                else
                  110
              else
                if a.val < 210 then
                  108
                else
                  111
            else
              if a.val < 213 then
                if a.val < 212 then
                  109
                else
                  106
              else
                if a.val < 214 then
                  104
                else
                  if a.val < 215 then
                    107
                  else
                    105
    else
      if a.val < 252 then
        if a.val < 234 then
          if a.val < 225 then
            if a.val < 220 then
              if a.val < 218 then
                if a.val < 217 then
                  102
                else
                  100
              else
                if a.val < 219 then
                  103
                else
                  101
            else
              if a.val < 222 then
                if a.val < 221 then
                  98
                else
                  96
              else
                if a.val < 223 then
                  99
                else
                  if a.val < 224 then
                    97
                  else
                    70
          else
            if a.val < 229 then
              if a.val < 227 then
                if a.val < 226 then
                  68
                else
                  71
              else
                if a.val < 228 then
                  69
                else
                  66
            else
              if a.val < 231 then
                if a.val < 230 then
                  64
                else
                  67
              else
                if a.val < 232 then
                  65
                else
                  if a.val < 233 then
                    78
                  else
                    76
        else
          if a.val < 243 then
            if a.val < 238 then
              if a.val < 236 then
                if a.val < 235 then
                  79
                else
                  77
              else
                if a.val < 237 then
                  74
                else
                  72
            else
              if a.val < 240 then
                if a.val < 239 then
                  75
                else
                  73
              else
                if a.val < 241 then
                  11
                else
                  if a.val < 242 then
                    9
                  else
                    10
          else
            if a.val < 247 then
              if a.val < 245 then
                if a.val < 244 then
                  8
                else
                  15
              else
                if a.val < 246 then
                  14
                else
                  13
            else
              if a.val < 249 then
                if a.val < 248 then
                  12
                else
                  19
              else
                if a.val < 250 then
                  17
                else
                  if a.val < 251 then
                    18
                  else
                    16
      else
        if a.val < 270 then
          if a.val < 261 then
            if a.val < 256 then
              if a.val < 254 then
                if a.val < 253 then
                  23
                else
                  22
              else
                if a.val < 255 then
                  21
                else
                  20
            else
              if a.val < 258 then
                if a.val < 257 then
                  27
                else
                  25
              else
                if a.val < 259 then
                  26
                else
                  if a.val < 260 then
                    24
                  else
                    31
          else
            if a.val < 265 then
              if a.val < 263 then
                if a.val < 262 then
                  30
                else
                  29
              else
                if a.val < 264 then
                  28
                else
                  35
            else
              if a.val < 267 then
                if a.val < 266 then
                  33
                else
                  34
              else
                if a.val < 268 then
                  32
                else
                  if a.val < 269 then
                    39
                  else
                    38
        else
          if a.val < 279 then
            if a.val < 274 then
              if a.val < 272 then
                if a.val < 271 then
                  37
                else
                  36
              else
                if a.val < 273 then
                  274
                else
                  275
            else
              if a.val < 276 then
                if a.val < 275 then
                  272
                else
                  273
              else
                if a.val < 277 then
                  277
                else
                  if a.val < 278 then
                    276
                  else
                    279
          else
            if a.val < 283 then
              if a.val < 281 then
                if a.val < 280 then
                  278
                else
                  282
              else
                if a.val < 282 then
                  283
                else
                  280
            else
              if a.val < 285 then
                if a.val < 284 then
                  281
                else
                  285
              else
                if a.val < 286 then
                  284
                else
                  if a.val < 287 then
                    287
                  else
                    286

def swap01Phase (a : Fin 288) : Fin 4 :=
  if a.val < 144 then
    if a.val < 72 then
      if a.val < 36 then
        if a.val < 18 then
          if a.val < 9 then
            if a.val < 4 then
              3
            else
              if a.val < 6 then
                3
              else
                if a.val < 7 then
                  3
                else
                  if a.val < 8 then
                    3
                  else
                    1
          else
            1
        else
          1
      else
        if a.val < 54 then
          if a.val < 45 then
            1
          else
            if a.val < 49 then
              if a.val < 47 then
                1
              else
                if a.val < 48 then
                  1
                else
                  3
            else
              3
        else
          3
    else
      if a.val < 108 then
        3
      else
        if a.val < 126 then
          if a.val < 117 then
            if a.val < 112 then
              3
            else
              0
          else
            0
        else
          0
  else
    if a.val < 216 then
      if a.val < 180 then
        if a.val < 162 then
          2
        else
          if a.val < 171 then
            2
          else
            if a.val < 175 then
              2
            else
              if a.val < 177 then
                if a.val < 176 then
                  2
                else
                  1
              else
                1
      else
        1
    else
      if a.val < 252 then
        if a.val < 234 then
          1
        else
          if a.val < 243 then
            if a.val < 238 then
              1
            else
              if a.val < 240 then
                1
              else
                3
          else
            3
      else
        if a.val < 270 then
          3
        else
          if a.val < 279 then
            if a.val < 274 then
              if a.val < 272 then
                3
              else
                0
            else
              0
          else
            0

def swap02Index (a : Fin 288) : Fin 288 :=
  if a.val < 144 then
    if a.val < 72 then
      if a.val < 36 then
        if a.val < 18 then
          if a.val < 9 then
            if a.val < 4 then
              if a.val < 2 then
                if a.val < 1 then
                  268
                else
                  269
              else
                if a.val < 3 then
                  270
                else
                  271
            else
              if a.val < 6 then
                if a.val < 5 then
                  267
                else
                  265
              else
                if a.val < 7 then
                  266
                else
                  if a.val < 8 then
                    264
                  else
                    39
          else
            if a.val < 13 then
              if a.val < 11 then
                if a.val < 10 then
                  38
                else
                  37
              else
                if a.val < 12 then
                  36
                else
                  32
            else
              if a.val < 15 then
                if a.val < 14 then
                  33
                else
                  34
              else
                if a.val < 16 then
                  35
                else
                  if a.val < 17 then
                    273
                  else
                    275
        else
          if a.val < 27 then
            if a.val < 22 then
              if a.val < 20 then
                if a.val < 19 then
                  272
                else
                  274
              else
                if a.val < 21 then
                  278
                else
                  279
            else
              if a.val < 24 then
                if a.val < 23 then
                  276
                else
                  277
              else
                if a.val < 25 then
                  281
                else
                  if a.val < 26 then
                    283
                  else
                    280
          else
            if a.val < 31 then
              if a.val < 29 then
                if a.val < 28 then
                  282
                else
                  286
              else
                if a.val < 30 then
                  287
                else
                  284
            else
              if a.val < 33 then
                if a.val < 32 then
                  285
                else
                  12
              else
                if a.val < 34 then
                  13
                else
                  if a.val < 35 then
                    14
                  else
                    15
      else
        if a.val < 54 then
          if a.val < 45 then
            if a.val < 40 then
              if a.val < 38 then
                if a.val < 37 then
                  11
                else
                  10
              else
                if a.val < 39 then
                  9
                else
                  8
            else
              if a.val < 42 then
                if a.val < 41 then
                  247
                else
                  246
              else
                if a.val < 43 then
                  245
                else
                  if a.val < 44 then
                    244
                  else
                    240
          else
            if a.val < 49 then
              if a.val < 47 then
                if a.val < 46 then
                  242
                else
                  241
              else
                if a.val < 48 then
                  243
                else
                  143
            else
              if a.val < 51 then
                if a.val < 50 then
                  141
                else
                  142
              else
                if a.val < 52 then
                  140
                else
                  if a.val < 53 then
                    139
                  else
                    137
        else
          if a.val < 63 then
            if a.val < 58 then
              if a.val < 56 then
                if a.val < 55 then
                  138
                else
                  136
              else
                if a.val < 57 then
                  135
                else
                  133
            else
              if a.val < 60 then
                if a.val < 59 then
                  134
                else
                  132
              else
                if a.val < 61 then
                  131
                else
                  if a.val < 62 then
                    129
                  else
                    130
          else
            if a.val < 67 then
              if a.val < 65 then
                if a.val < 64 then
                  128
                else
                  66
              else
                if a.val < 66 then
                  67
                else
                  64
            else
              if a.val < 69 then
                if a.val < 68 then
                  65
                else
                  70
              else
                if a.val < 70 then
                  71
                else
                  if a.val < 71 then
                    68
                  else
                    69
    else
      if a.val < 108 then
        if a.val < 90 then
          if a.val < 81 then
            if a.val < 76 then
              if a.val < 74 then
                if a.val < 73 then
                  74
                else
                  75
              else
                if a.val < 75 then
                  72
                else
                  73
            else
              if a.val < 78 then
                if a.val < 77 then
                  78
                else
                  79
              else
                if a.val < 79 then
                  76
                else
                  if a.val < 80 then
                    77
                  else
                    219
          else
            if a.val < 85 then
              if a.val < 83 then
                if a.val < 82 then
                  218
                else
                  217
              else
                if a.val < 84 then
                  216
                else
                  223
            else
              if a.val < 87 then
                if a.val < 86 then
                  222
                else
                  221
              else
                if a.val < 88 then
                  220
                else
                  if a.val < 89 then
                    211
                  else
                    210
        else
          if a.val < 99 then
            if a.val < 94 then
              if a.val < 92 then
                if a.val < 91 then
                  209
                else
                  208
              else
                if a.val < 93 then
                  215
                else
                  214
            else
              if a.val < 96 then
                if a.val < 95 then
                  213
                else
                  212
              else
                if a.val < 97 then
                  150
                else
                  if a.val < 98 then
                    148
                  else
                    151
          else
            if a.val < 103 then
              if a.val < 101 then
                if a.val < 100 then
                  149
                else
                  146
              else
                if a.val < 102 then
                  144
                else
                  147
            else
              if a.val < 105 then
                if a.val < 104 then
                  145
                else
                  158
              else
                if a.val < 106 then
                  156
                else
                  if a.val < 107 then
                    159
                  else
                    157
      else
        if a.val < 126 then
          if a.val < 117 then
            if a.val < 112 then
              if a.val < 110 then
                if a.val < 109 then
                  154
                else
                  152
              else
                if a.val < 111 then
                  155
                else
                  153
            else
              if a.val < 114 then
                if a.val < 113 then
                  228
                else
                  230
              else
                if a.val < 115 then
                  229
                else
                  if a.val < 116 then
                    231
                  else
                    224
          else
            if a.val < 121 then
              if a.val < 119 then
                if a.val < 118 then
                  226
                else
                  225
              else
                if a.val < 120 then
                  227
                else
                  236
            else
              if a.val < 123 then
                if a.val < 122 then
                  238
                else
                  237
              else
                if a.val < 124 then
                  239
                else
                  if a.val < 125 then
                    232
                  else
                    234
        else
          if a.val < 135 then
            if a.val < 130 then
              if a.val < 128 then
                if a.val < 127 then
                  233
                else
                  235
              else
                if a.val < 129 then
                  63
                else
                  61
            else
              if a.val < 132 then
                if a.val < 131 then
                  62
                else
                  60
              else
                if a.val < 133 then
                  59
                else
                  if a.val < 134 then
                    57
                  else
                    58
          else
            if a.val < 139 then
              if a.val < 137 then
                if a.val < 136 then
                  56
                else
                  55
              else
                if a.val < 138 then
                  53
                else
                  54
            else
              if a.val < 141 then
                if a.val < 140 then
                  52
                else
                  51
              else
                if a.val < 142 then
                  49
                else
                  if a.val < 143 then
                    50
                  else
                    48
  else
    if a.val < 216 then
      if a.val < 180 then
        if a.val < 162 then
          if a.val < 153 then
            if a.val < 148 then
              if a.val < 146 then
                if a.val < 145 then
                  101
                else
                  103
              else
                if a.val < 147 then
                  100
                else
                  102
            else
              if a.val < 150 then
                if a.val < 149 then
                  97
                else
                  99
              else
                if a.val < 151 then
                  96
                else
                  if a.val < 152 then
                    98
                  else
                    109
          else
            if a.val < 157 then
              if a.val < 155 then
                if a.val < 154 then
                  111
                else
                  108
              else
                if a.val < 156 then
                  110
                else
                  105
            else
              if a.val < 159 then
                if a.val < 158 then
                  107
                else
                  104
              else
                if a.val < 160 then
                  106
                else
                  if a.val < 161 then
                    190
                  else
                    188
        else
          if a.val < 171 then
            if a.val < 166 then
              if a.val < 164 then
                if a.val < 163 then
                  191
                else
                  189
              else
                if a.val < 165 then
                  186
                else
                  184
            else
              if a.val < 168 then
                if a.val < 167 then
                  187
                else
                  185
              else
                if a.val < 169 then
                  182
                else
                  if a.val < 170 then
                    180
                  else
                    183
          else
            if a.val < 175 then
              if a.val < 173 then
                if a.val < 172 then
                  181
                else
                  178
              else
                if a.val < 174 then
                  176
                else
                  179
            else
              if a.val < 177 then
                if a.val < 176 then
                  177
                else
                  173
              else
                if a.val < 178 then
                  175
                else
                  if a.val < 179 then
                    172
                  else
                    174
      else
        if a.val < 198 then
          if a.val < 189 then
            if a.val < 184 then
              if a.val < 182 then
                if a.val < 181 then
                  169
                else
                  171
              else
                if a.val < 183 then
                  168
                else
                  170
            else
              if a.val < 186 then
                if a.val < 185 then
                  165
                else
                  167
              else
                if a.val < 187 then
                  164
                else
                  if a.val < 188 then
                    166
                  else
                    161
          else
            if a.val < 193 then
              if a.val < 191 then
                if a.val < 190 then
                  163
                else
                  160
              else
                if a.val < 192 then
                  162
                else
                  194
            else
              if a.val < 195 then
                if a.val < 194 then
                  195
                else
                  192
              else
                if a.val < 196 then
                  193
                else
                  if a.val < 197 then
                    198
                  else
                    199
        else
          if a.val < 207 then
            if a.val < 202 then
              if a.val < 200 then
                if a.val < 199 then
                  196
                else
                  197
              else
                if a.val < 201 then
                  202
                else
                  203
            else
              if a.val < 204 then
                if a.val < 203 then
                  200
                else
                  201
              else
                if a.val < 205 then
                  206
                else
                  if a.val < 206 then
                    207
                  else
                    204
          else
            if a.val < 211 then
              if a.val < 209 then
                if a.val < 208 then
                  205
                else
                  91
              else
                if a.val < 210 then
                  90
                else
                  89
            else
              if a.val < 213 then
                if a.val < 212 then
                  88
                else
                  95
              else
                if a.val < 214 then
                  94
                else
                  if a.val < 215 then
                    93
                  else
                    92
    else
      if a.val < 252 then
        if a.val < 234 then
          if a.val < 225 then
            if a.val < 220 then
              if a.val < 218 then
                if a.val < 217 then
                  83
                else
                  82
              else
                if a.val < 219 then
                  81
                else
                  80
            else
              if a.val < 222 then
                if a.val < 221 then
                  87
                else
                  86
              else
                if a.val < 223 then
                  85
                else
                  if a.val < 224 then
                    84
                  else
                    116
          else
            if a.val < 229 then
              if a.val < 227 then
                if a.val < 226 then
                  118
                else
                  117
              else
                if a.val < 228 then
                  119
                else
                  112
            else
              if a.val < 231 then
                if a.val < 230 then
                  114
                else
                  113
              else
                if a.val < 232 then
                  115
                else
                  if a.val < 233 then
                    124
                  else
                    126
        else
          if a.val < 243 then
            if a.val < 238 then
              if a.val < 236 then
                if a.val < 235 then
                  125
                else
                  127
              else
                if a.val < 237 then
                  120
                else
                  122
            else
              if a.val < 240 then
                if a.val < 239 then
                  121
                else
                  123
              else
                if a.val < 241 then
                  44
                else
                  if a.val < 242 then
                    46
                  else
                    45
          else
            if a.val < 247 then
              if a.val < 245 then
                if a.val < 244 then
                  47
                else
                  43
              else
                if a.val < 246 then
                  42
                else
                  41
            else
              if a.val < 249 then
                if a.val < 248 then
                  40
                else
                  250
              else
                if a.val < 250 then
                  251
                else
                  if a.val < 251 then
                    248
                  else
                    249
      else
        if a.val < 270 then
          if a.val < 261 then
            if a.val < 256 then
              if a.val < 254 then
                if a.val < 253 then
                  253
                else
                  252
              else
                if a.val < 255 then
                  255
                else
                  254
            else
              if a.val < 258 then
                if a.val < 257 then
                  258
                else
                  259
              else
                if a.val < 259 then
                  256
                else
                  if a.val < 260 then
                    257
                  else
                    261
          else
            if a.val < 265 then
              if a.val < 263 then
                if a.val < 262 then
                  260
                else
                  263
              else
                if a.val < 264 then
                  262
                else
                  7
            else
              if a.val < 267 then
                if a.val < 266 then
                  5
                else
                  6
              else
                if a.val < 268 then
                  4
                else
                  if a.val < 269 then
                    0
                  else
                    1
        else
          if a.val < 279 then
            if a.val < 274 then
              if a.val < 272 then
                if a.val < 271 then
                  2
                else
                  3
              else
                if a.val < 273 then
                  18
                else
                  16
            else
              if a.val < 276 then
                if a.val < 275 then
                  19
                else
                  17
              else
                if a.val < 277 then
                  22
                else
                  if a.val < 278 then
                    23
                  else
                    20
          else
            if a.val < 283 then
              if a.val < 281 then
                if a.val < 280 then
                  21
                else
                  26
              else
                if a.val < 282 then
                  24
                else
                  27
            else
              if a.val < 285 then
                if a.val < 284 then
                  25
                else
                  30
              else
                if a.val < 286 then
                  31
                else
                  if a.val < 287 then
                    28
                  else
                    29

def swap02Phase (a : Fin 288) : Fin 4 :=
  if a.val < 144 then
    if a.val < 72 then
      if a.val < 36 then
        if a.val < 18 then
          if a.val < 9 then
            if a.val < 4 then
              0
            else
              if a.val < 6 then
                0
              else
                if a.val < 7 then
                  0
                else
                  if a.val < 8 then
                    0
                  else
                    3
          else
            if a.val < 13 then
              3
            else
              if a.val < 15 then
                3
              else
                if a.val < 16 then
                  3
                else
                  1
        else
          1
      else
        if a.val < 54 then
          if a.val < 45 then
            if a.val < 40 then
              1
            else
              2
          else
            if a.val < 49 then
              if a.val < 47 then
                2
              else
                if a.val < 48 then
                  2
                else
                  3
            else
              3
        else
          if a.val < 63 then
            3
          else
            if a.val < 67 then
              if a.val < 65 then
                if a.val < 64 then
                  3
                else
                  0
              else
                0
            else
              0
    else
      if a.val < 108 then
        if a.val < 90 then
          if a.val < 81 then
            if a.val < 76 then
              0
            else
              if a.val < 78 then
                0
              else
                if a.val < 79 then
                  0
                else
                  if a.val < 80 then
                    0
                  else
                    2
          else
            2
        else
          if a.val < 99 then
            if a.val < 94 then
              2
            else
              if a.val < 96 then
                2
              else
                1
          else
            1
      else
        if a.val < 126 then
          if a.val < 117 then
            if a.val < 112 then
              1
            else
              3
          else
            3
        else
          if a.val < 135 then
            if a.val < 130 then
              if a.val < 128 then
                3
              else
                1
            else
              1
          else
            1
  else
    if a.val < 216 then
      if a.val < 180 then
        if a.val < 162 then
          if a.val < 153 then
            3
          else
            if a.val < 157 then
              3
            else
              if a.val < 159 then
                3
              else
                if a.val < 160 then
                  3
                else
                  1
        else
          if a.val < 171 then
            1
          else
            if a.val < 175 then
              1
            else
              if a.val < 177 then
                if a.val < 176 then
                  1
                else
                  3
              else
                3
      else
        if a.val < 198 then
          if a.val < 189 then
            3
          else
            if a.val < 193 then
              if a.val < 191 then
                3
              else
                if a.val < 192 then
                  3
                else
                  0
            else
              0
        else
          if a.val < 207 then
            0
          else
            if a.val < 211 then
              if a.val < 209 then
                if a.val < 208 then
                  0
                else
                  2
              else
                2
            else
              2
    else
      if a.val < 252 then
        if a.val < 234 then
          if a.val < 225 then
            if a.val < 220 then
              2
            else
              if a.val < 222 then
                2
              else
                if a.val < 223 then
                  2
                else
                  if a.val < 224 then
                    2
                  else
                    1
          else
            1
        else
          if a.val < 243 then
            if a.val < 238 then
              1
            else
              if a.val < 240 then
                1
              else
                2
          else
            if a.val < 247 then
              2
            else
              if a.val < 249 then
                if a.val < 248 then
                  2
                else
                  0
              else
                0
      else
        if a.val < 270 then
          0
        else
          if a.val < 279 then
            if a.val < 274 then
              if a.val < 272 then
                0
              else
                3
            else
              3
          else
            3

def swap03Index (a : Fin 288) : Fin 288 :=
  if a.val < 144 then
    if a.val < 72 then
      if a.val < 36 then
        if a.val < 18 then
          if a.val < 9 then
            if a.val < 4 then
              if a.val < 2 then
                if a.val < 1 then
                  261
                else
                  260
              else
                if a.val < 3 then
                  263
                else
                  262
            else
              if a.val < 6 then
                if a.val < 5 then
                  257
                else
                  259
              else
                if a.val < 7 then
                  256
                else
                  if a.val < 8 then
                    258
                  else
                    285
          else
            if a.val < 13 then
              if a.val < 11 then
                if a.val < 10 then
                  284
                else
                  287
              else
                if a.val < 12 then
                  286
                else
                  281
            else
              if a.val < 15 then
                if a.val < 14 then
                  283
                else
                  280
              else
                if a.val < 16 then
                  282
                else
                  if a.val < 17 then
                    31
                  else
                    30
        else
          if a.val < 27 then
            if a.val < 22 then
              if a.val < 20 then
                if a.val < 19 then
                  29
                else
                  28
              else
                if a.val < 21 then
                  24
                else
                  25
            else
              if a.val < 24 then
                if a.val < 23 then
                  26
                else
                  27
              else
                if a.val < 25 then
                  20
                else
                  if a.val < 26 then
                    21
                  else
                    22
          else
            if a.val < 31 then
              if a.val < 29 then
                if a.val < 28 then
                  23
                else
                  19
              else
                if a.val < 30 then
                  18
                else
                  17
            else
              if a.val < 33 then
                if a.val < 32 then
                  16
                else
                  278
              else
                if a.val < 34 then
                  279
                else
                  if a.val < 35 then
                    276
                  else
                    277
      else
        if a.val < 54 then
          if a.val < 45 then
            if a.val < 40 then
              if a.val < 38 then
                if a.val < 37 then
                  274
                else
                  272
              else
                if a.val < 39 then
                  275
                else
                  273
            else
              if a.val < 42 then
                if a.val < 41 then
                  254
                else
                  255
              else
                if a.val < 43 then
                  252
                else
                  if a.val < 44 then
                    253
                  else
                    250
          else
            if a.val < 49 then
              if a.val < 47 then
                if a.val < 46 then
                  248
                else
                  251
              else
                if a.val < 48 then
                  249
                else
                  50
            else
              if a.val < 51 then
                if a.val < 50 then
                  51
                else
                  48
              else
                if a.val < 52 then
                  49
                else
                  if a.val < 53 then
                    54
                  else
                    55
        else
          if a.val < 63 then
            if a.val < 58 then
              if a.val < 56 then
                if a.val < 55 then
                  52
                else
                  53
              else
                if a.val < 57 then
                  235
                else
                  234
            else
              if a.val < 60 then
                if a.val < 59 then
                  233
                else
                  232
              else
                if a.val < 61 then
                  239
                else
                  if a.val < 62 then
                    238
                  else
                    237
          else
            if a.val < 67 then
              if a.val < 65 then
                if a.val < 64 then
                  236
                else
                  142
              else
                if a.val < 66 then
                  140
                else
                  143
            else
              if a.val < 69 then
                if a.val < 68 then
                  141
                else
                  138
              else
                if a.val < 70 then
                  136
                else
                  if a.val < 71 then
                    139
                  else
                    137
    else
      if a.val < 108 then
        if a.val < 90 then
          if a.val < 81 then
            if a.val < 76 then
              if a.val < 74 then
                if a.val < 73 then
                  151
                else
                  149
              else
                if a.val < 75 then
                  150
                else
                  148
            else
              if a.val < 78 then
                if a.val < 77 then
                  147
                else
                  145
              else
                if a.val < 79 then
                  146
                else
                  if a.val < 80 then
                    144
                  else
                    127
          else
            if a.val < 85 then
              if a.val < 83 then
                if a.val < 82 then
                  125
                else
                  126
              else
                if a.val < 84 then
                  124
                else
                  123
            else
              if a.val < 87 then
                if a.val < 86 then
                  121
                else
                  122
              else
                if a.val < 88 then
                  120
                else
                  if a.val < 89 then
                    166
                  else
                    164
        else
          if a.val < 99 then
            if a.val < 94 then
              if a.val < 92 then
                if a.val < 91 then
                  167
                else
                  165
              else
                if a.val < 93 then
                  162
                else
                  160
            else
              if a.val < 96 then
                if a.val < 95 then
                  163
                else
                  161
              else
                if a.val < 97 then
                  98
                else
                  if a.val < 98 then
                    99
                  else
                    96
          else
            if a.val < 103 then
              if a.val < 101 then
                if a.val < 100 then
                  97
                else
                  102
              else
                if a.val < 102 then
                  103
                else
                  100
            else
              if a.val < 105 then
                if a.val < 104 then
                  101
                else
                  187
              else
                if a.val < 106 then
                  186
                else
                  if a.val < 107 then
                    185
                  else
                    184
      else
        if a.val < 126 then
          if a.val < 117 then
            if a.val < 112 then
              if a.val < 110 then
                if a.val < 109 then
                  191
                else
                  190
              else
                if a.val < 111 then
                  189
                else
                  188
            else
              if a.val < 114 then
                if a.val < 113 then
                  206
                else
                  204
              else
                if a.val < 115 then
                  207
                else
                  if a.val < 116 then
                    205
                  else
                    202
          else
            if a.val < 121 then
              if a.val < 119 then
                if a.val < 118 then
                  200
                else
                  203
              else
                if a.val < 120 then
                  201
                else
                  87
            else
              if a.val < 123 then
                if a.val < 122 then
                  85
                else
                  86
              else
                if a.val < 124 then
                  84
                else
                  if a.val < 125 then
                    83
                  else
                    81
        else
          if a.val < 135 then
            if a.val < 130 then
              if a.val < 128 then
                if a.val < 127 then
                  82
                else
                  80
              else
                if a.val < 129 then
                  220
                else
                  222
            else
              if a.val < 132 then
                if a.val < 131 then
                  221
                else
                  223
              else
                if a.val < 133 then
                  216
                else
                  if a.val < 134 then
                    218
                  else
                    217
          else
            if a.val < 139 then
              if a.val < 137 then
                if a.val < 136 then
                  219
                else
                  69
              else
                if a.val < 138 then
                  71
                else
                  68
            else
              if a.val < 141 then
                if a.val < 140 then
                  70
                else
                  65
              else
                if a.val < 142 then
                  67
                else
                  if a.val < 143 then
                    64
                  else
                    66
  else
    if a.val < 216 then
      if a.val < 180 then
        if a.val < 162 then
          if a.val < 153 then
            if a.val < 148 then
              if a.val < 146 then
                if a.val < 145 then
                  79
                else
                  77
              else
                if a.val < 147 then
                  78
                else
                  76
            else
              if a.val < 150 then
                if a.val < 149 then
                  75
                else
                  73
              else
                if a.val < 151 then
                  74
                else
                  if a.val < 152 then
                    72
                  else
                    214
          else
            if a.val < 157 then
              if a.val < 155 then
                if a.val < 154 then
                  212
                else
                  215
              else
                if a.val < 156 then
                  213
                else
                  210
            else
              if a.val < 159 then
                if a.val < 158 then
                  208
                else
                  211
              else
                if a.val < 160 then
                  209
                else
                  if a.val < 161 then
                    93
                  else
                    95
        else
          if a.val < 171 then
            if a.val < 166 then
              if a.val < 164 then
                if a.val < 163 then
                  92
                else
                  94
              else
                if a.val < 165 then
                  89
                else
                  91
            else
              if a.val < 168 then
                if a.val < 167 then
                  88
                else
                  90
              else
                if a.val < 169 then
                  196
                else
                  if a.val < 170 then
                    198
                  else
                    197
          else
            if a.val < 175 then
              if a.val < 173 then
                if a.val < 172 then
                  199
                else
                  192
              else
                if a.val < 174 then
                  194
                else
                  193
            else
              if a.val < 177 then
                if a.val < 176 then
                  195
                else
                  178
              else
                if a.val < 178 then
                  179
                else
                  if a.val < 179 then
                    176
                  else
                    177
      else
        if a.val < 198 then
          if a.val < 189 then
            if a.val < 184 then
              if a.val < 182 then
                if a.val < 181 then
                  182
                else
                  183
              else
                if a.val < 183 then
                  180
                else
                  181
            else
              if a.val < 186 then
                if a.val < 185 then
                  107
                else
                  106
              else
                if a.val < 187 then
                  105
                else
                  if a.val < 188 then
                    104
                  else
                    111
          else
            if a.val < 193 then
              if a.val < 191 then
                if a.val < 190 then
                  110
                else
                  109
              else
                if a.val < 192 then
                  108
                else
                  172
            else
              if a.val < 195 then
                if a.val < 194 then
                  174
                else
                  173
              else
                if a.val < 196 then
                  175
                else
                  if a.val < 197 then
                    168
                  else
                    170
        else
          if a.val < 207 then
            if a.val < 202 then
              if a.val < 200 then
                if a.val < 199 then
                  169
                else
                  171
              else
                if a.val < 201 then
                  117
                else
                  119
            else
              if a.val < 204 then
                if a.val < 203 then
                  116
                else
                  118
              else
                if a.val < 205 then
                  113
                else
                  if a.val < 206 then
                    115
                  else
                    112
          else
            if a.val < 211 then
              if a.val < 209 then
                if a.val < 208 then
                  114
                else
                  157
              else
                if a.val < 210 then
                  159
                else
                  156
            else
              if a.val < 213 then
                if a.val < 212 then
                  158
                else
                  153
              else
                if a.val < 214 then
                  155
                else
                  if a.val < 215 then
                    152
                  else
                    154
    else
      if a.val < 252 then
        if a.val < 234 then
          if a.val < 225 then
            if a.val < 220 then
              if a.val < 218 then
                if a.val < 217 then
                  132
                else
                  134
              else
                if a.val < 219 then
                  133
                else
                  135
            else
              if a.val < 222 then
                if a.val < 221 then
                  128
                else
                  130
              else
                if a.val < 223 then
                  129
                else
                  if a.val < 224 then
                    131
                  else
                    226
          else
            if a.val < 229 then
              if a.val < 227 then
                if a.val < 226 then
                  227
                else
                  224
              else
                if a.val < 228 then
                  225
                else
                  230
            else
              if a.val < 231 then
                if a.val < 230 then
                  231
                else
                  228
              else
                if a.val < 232 then
                  229
                else
                  if a.val < 233 then
                    59
                  else
                    58
        else
          if a.val < 243 then
            if a.val < 238 then
              if a.val < 236 then
                if a.val < 235 then
                  57
                else
                  56
              else
                if a.val < 237 then
                  63
                else
                  62
            else
              if a.val < 240 then
                if a.val < 239 then
                  61
                else
                  60
              else
                if a.val < 241 then
                  242
                else
                  if a.val < 242 then
                    243
                  else
                    240
          else
            if a.val < 247 then
              if a.val < 245 then
                if a.val < 244 then
                  241
                else
                  245
              else
                if a.val < 246 then
                  244
                else
                  247
            else
              if a.val < 249 then
                if a.val < 248 then
                  246
                else
                  45
              else
                if a.val < 250 then
                  47
                else
                  if a.val < 251 then
                    44
                  else
                    46
      else
        if a.val < 270 then
          if a.val < 261 then
            if a.val < 256 then
              if a.val < 254 then
                if a.val < 253 then
                  42
                else
                  43
              else
                if a.val < 255 then
                  40
                else
                  41
            else
              if a.val < 258 then
                if a.val < 257 then
                  6
                else
                  4
              else
                if a.val < 259 then
                  7
                else
                  if a.val < 260 then
                    5
                  else
                    1
          else
            if a.val < 265 then
              if a.val < 263 then
                if a.val < 262 then
                  0
                else
                  3
              else
                if a.val < 264 then
                  2
                else
                  266
            else
              if a.val < 267 then
                if a.val < 266 then
                  267
                else
                  264
              else
                if a.val < 268 then
                  265
                else
                  if a.val < 269 then
                    269
                  else
                    268
        else
          if a.val < 279 then
            if a.val < 274 then
              if a.val < 272 then
                if a.val < 271 then
                  271
                else
                  270
              else
                if a.val < 273 then
                  37
                else
                  39
            else
              if a.val < 276 then
                if a.val < 275 then
                  36
                else
                  38
              else
                if a.val < 277 then
                  34
                else
                  if a.val < 278 then
                    35
                  else
                    32
          else
            if a.val < 283 then
              if a.val < 281 then
                if a.val < 280 then
                  33
                else
                  14
              else
                if a.val < 282 then
                  12
                else
                  15
            else
              if a.val < 285 then
                if a.val < 284 then
                  13
                else
                  9
              else
                if a.val < 286 then
                  8
                else
                  if a.val < 287 then
                    11
                  else
                    10

def swap03Phase (a : Fin 288) : Fin 4 :=
  if a.val < 144 then
    if a.val < 72 then
      if a.val < 36 then
        if a.val < 18 then
          if a.val < 9 then
            0
          else
            if a.val < 13 then
              0
            else
              if a.val < 15 then
                0
              else
                if a.val < 16 then
                  0
                else
                  3
        else
          if a.val < 27 then
            if a.val < 22 then
              3
            else
              if a.val < 24 then
                3
              else
                1
          else
            if a.val < 31 then
              1
            else
              if a.val < 33 then
                if a.val < 32 then
                  1
                else
                  2
              else
                2
      else
        if a.val < 54 then
          if a.val < 45 then
            2
          else
            if a.val < 49 then
              if a.val < 47 then
                2
              else
                if a.val < 48 then
                  2
                else
                  0
            else
              0
        else
          if a.val < 63 then
            if a.val < 58 then
              if a.val < 56 then
                0
              else
                2
            else
              2
          else
            if a.val < 67 then
              if a.val < 65 then
                if a.val < 64 then
                  2
                else
                  3
              else
                3
            else
              3
    else
      if a.val < 108 then
        if a.val < 90 then
          if a.val < 81 then
            if a.val < 76 then
              1
            else
              if a.val < 78 then
                1
              else
                if a.val < 79 then
                  1
                else
                  if a.val < 80 then
                    1
                  else
                    3
          else
            if a.val < 85 then
              3
            else
              if a.val < 87 then
                3
              else
                if a.val < 88 then
                  3
                else
                  1
        else
          if a.val < 99 then
            if a.val < 94 then
              1
            else
              if a.val < 96 then
                1
              else
                0
          else
            if a.val < 103 then
              0
            else
              if a.val < 105 then
                if a.val < 104 then
                  0
                else
                  2
              else
                2
      else
        if a.val < 126 then
          if a.val < 117 then
            if a.val < 112 then
              2
            else
              3
          else
            if a.val < 121 then
              if a.val < 119 then
                3
              else
                if a.val < 120 then
                  3
                else
                  1
            else
              1
        else
          if a.val < 135 then
            if a.val < 130 then
              if a.val < 128 then
                1
              else
                3
            else
              3
          else
            if a.val < 139 then
              if a.val < 137 then
                if a.val < 136 then
                  3
                else
                  1
              else
                1
            else
              1
  else
    if a.val < 216 then
      if a.val < 180 then
        if a.val < 162 then
          if a.val < 153 then
            if a.val < 148 then
              3
            else
              if a.val < 150 then
                3
              else
                if a.val < 151 then
                  3
                else
                  if a.val < 152 then
                    3
                  else
                    1
          else
            if a.val < 157 then
              1
            else
              if a.val < 159 then
                1
              else
                if a.val < 160 then
                  1
                else
                  3
        else
          if a.val < 171 then
            if a.val < 166 then
              3
            else
              if a.val < 168 then
                3
              else
                1
          else
            if a.val < 175 then
              1
            else
              if a.val < 177 then
                if a.val < 176 then
                  1
                else
                  0
              else
                0
      else
        if a.val < 198 then
          if a.val < 189 then
            if a.val < 184 then
              0
            else
              2
          else
            if a.val < 193 then
              if a.val < 191 then
                2
              else
                if a.val < 192 then
                  2
                else
                  3
            else
              3
        else
          if a.val < 207 then
            if a.val < 202 then
              if a.val < 200 then
                3
              else
                1
            else
              1
          else
            if a.val < 211 then
              if a.val < 209 then
                if a.val < 208 then
                  1
                else
                  3
              else
                3
            else
              3
    else
      if a.val < 252 then
        if a.val < 234 then
          if a.val < 225 then
            if a.val < 220 then
              1
            else
              if a.val < 222 then
                1
              else
                if a.val < 223 then
                  1
                else
                  if a.val < 224 then
                    1
                  else
                    0
          else
            if a.val < 229 then
              0
            else
              if a.val < 231 then
                0
              else
                if a.val < 232 then
                  0
                else
                  2
        else
          if a.val < 243 then
            if a.val < 238 then
              2
            else
              if a.val < 240 then
                2
              else
                0
          else
            if a.val < 247 then
              0
            else
              if a.val < 249 then
                if a.val < 248 then
                  0
                else
                  2
              else
                2
      else
        if a.val < 270 then
          if a.val < 261 then
            if a.val < 256 then
              2
            else
              0
          else
            0
        else
          if a.val < 279 then
            if a.val < 274 then
              if a.val < 272 then
                0
              else
                2
            else
              2
          else
            if a.val < 283 then
              if a.val < 281 then
                if a.val < 280 then
                  2
                else
                  0
              else
                0
            else
              0

def swap12Index (a : Fin 288) : Fin 288 :=
  if a.val < 144 then
    if a.val < 72 then
      if a.val < 36 then
        if a.val < 18 then
          if a.val < 9 then
            if a.val < 4 then
              if a.val < 2 then
                if a.val < 1 then
                  8
                else
                  9
              else
                if a.val < 3 then
                  10
                else
                  11
            else
              if a.val < 6 then
                if a.val < 5 then
                  12
                else
                  13
              else
                if a.val < 7 then
                  14
                else
                  if a.val < 8 then
                    15
                  else
                    0
          else
            if a.val < 13 then
              if a.val < 11 then
                if a.val < 10 then
                  1
                else
                  2
              else
                if a.val < 12 then
                  3
                else
                  4
            else
              if a.val < 15 then
                if a.val < 14 then
                  5
                else
                  6
              else
                if a.val < 16 then
                  7
                else
                  if a.val < 17 then
                    17
                  else
                    16
        else
          if a.val < 27 then
            if a.val < 22 then
              if a.val < 20 then
                if a.val < 19 then
                  19
                else
                  18
              else
                if a.val < 21 then
                  21
                else
                  20
            else
              if a.val < 24 then
                if a.val < 23 then
                  23
                else
                  22
              else
                if a.val < 25 then
                  25
                else
                  if a.val < 26 then
                    24
                  else
                    27
          else
            if a.val < 31 then
              if a.val < 29 then
                if a.val < 28 then
                  26
                else
                  29
              else
                if a.val < 30 then
                  28
                else
                  31
            else
              if a.val < 33 then
                if a.val < 32 then
                  30
                else
                  40
              else
                if a.val < 34 then
                  41
                else
                  if a.val < 35 then
                    42
                  else
                    43
      else
        if a.val < 54 then
          if a.val < 45 then
            if a.val < 40 then
              if a.val < 38 then
                if a.val < 37 then
                  44
                else
                  45
              else
                if a.val < 39 then
                  46
                else
                  47
            else
              if a.val < 42 then
                if a.val < 41 then
                  32
                else
                  33
              else
                if a.val < 43 then
                  34
                else
                  if a.val < 44 then
                    35
                  else
                    36
          else
            if a.val < 49 then
              if a.val < 47 then
                if a.val < 46 then
                  37
                else
                  38
              else
                if a.val < 48 then
                  39
                else
                  49
            else
              if a.val < 51 then
                if a.val < 50 then
                  48
                else
                  51
              else
                if a.val < 52 then
                  50
                else
                  if a.val < 53 then
                    53
                  else
                    52
        else
          if a.val < 63 then
            if a.val < 58 then
              if a.val < 56 then
                if a.val < 55 then
                  55
                else
                  54
              else
                if a.val < 57 then
                  57
                else
                  56
            else
              if a.val < 60 then
                if a.val < 59 then
                  59
                else
                  58
              else
                if a.val < 61 then
                  61
                else
                  if a.val < 62 then
                    60
                  else
                    63
          else
            if a.val < 67 then
              if a.val < 65 then
                if a.val < 64 then
                  62
                else
                  112
              else
                if a.val < 66 then
                  113
                else
                  114
            else
              if a.val < 69 then
                if a.val < 68 then
                  115
                else
                  116
              else
                if a.val < 70 then
                  117
                else
                  if a.val < 71 then
                    118
                  else
                    119
    else
      if a.val < 108 then
        if a.val < 90 then
          if a.val < 81 then
            if a.val < 76 then
              if a.val < 74 then
                if a.val < 73 then
                  120
                else
                  121
              else
                if a.val < 75 then
                  122
                else
                  123
            else
              if a.val < 78 then
                if a.val < 77 then
                  124
                else
                  125
              else
                if a.val < 79 then
                  126
                else
                  if a.val < 80 then
                    127
                  else
                    144
          else
            if a.val < 85 then
              if a.val < 83 then
                if a.val < 82 then
                  145
                else
                  146
              else
                if a.val < 84 then
                  147
                else
                  148
            else
              if a.val < 87 then
                if a.val < 86 then
                  149
                else
                  150
              else
                if a.val < 88 then
                  151
                else
                  if a.val < 89 then
                    152
                  else
                    153
        else
          if a.val < 99 then
            if a.val < 94 then
              if a.val < 92 then
                if a.val < 91 then
                  154
                else
                  155
              else
                if a.val < 93 then
                  156
                else
                  157
            else
              if a.val < 96 then
                if a.val < 95 then
                  158
                else
                  159
              else
                if a.val < 97 then
                  176
                else
                  if a.val < 98 then
                    177
                  else
                    178
          else
            if a.val < 103 then
              if a.val < 101 then
                if a.val < 100 then
                  179
                else
                  180
              else
                if a.val < 102 then
                  181
                else
                  182
            else
              if a.val < 105 then
                if a.val < 104 then
                  183
                else
                  184
              else
                if a.val < 106 then
                  185
                else
                  if a.val < 107 then
                    186
                  else
                    187
      else
        if a.val < 126 then
          if a.val < 117 then
            if a.val < 112 then
              if a.val < 110 then
                if a.val < 109 then
                  188
                else
                  189
              else
                if a.val < 111 then
                  190
                else
                  191
            else
              if a.val < 114 then
                if a.val < 113 then
                  64
                else
                  65
              else
                if a.val < 115 then
                  66
                else
                  if a.val < 116 then
                    67
                  else
                    68
          else
            if a.val < 121 then
              if a.val < 119 then
                if a.val < 118 then
                  69
                else
                  70
              else
                if a.val < 120 then
                  71
                else
                  72
            else
              if a.val < 123 then
                if a.val < 122 then
                  73
                else
                  74
              else
                if a.val < 124 then
                  75
                else
                  if a.val < 125 then
                    76
                  else
                    77
        else
          if a.val < 135 then
            if a.val < 130 then
              if a.val < 128 then
                if a.val < 127 then
                  78
                else
                  79
              else
                if a.val < 129 then
                  192
                else
                  193
            else
              if a.val < 132 then
                if a.val < 131 then
                  194
                else
                  195
              else
                if a.val < 133 then
                  196
                else
                  if a.val < 134 then
                    197
                  else
                    198
          else
            if a.val < 139 then
              if a.val < 137 then
                if a.val < 136 then
                  199
                else
                  200
              else
                if a.val < 138 then
                  201
                else
                  202
            else
              if a.val < 141 then
                if a.val < 140 then
                  203
                else
                  204
              else
                if a.val < 142 then
                  205
                else
                  if a.val < 143 then
                    206
                  else
                    207
  else
    if a.val < 216 then
      if a.val < 180 then
        if a.val < 162 then
          if a.val < 153 then
            if a.val < 148 then
              if a.val < 146 then
                if a.val < 145 then
                  80
                else
                  81
              else
                if a.val < 147 then
                  82
                else
                  83
            else
              if a.val < 150 then
                if a.val < 149 then
                  84
                else
                  85
              else
                if a.val < 151 then
                  86
                else
                  if a.val < 152 then
                    87
                  else
                    88
          else
            if a.val < 157 then
              if a.val < 155 then
                if a.val < 154 then
                  89
                else
                  90
              else
                if a.val < 156 then
                  91
                else
                  92
            else
              if a.val < 159 then
                if a.val < 158 then
                  93
                else
                  94
              else
                if a.val < 160 then
                  95
                else
                  if a.val < 161 then
                    208
                  else
                    209
        else
          if a.val < 171 then
            if a.val < 166 then
              if a.val < 164 then
                if a.val < 163 then
                  210
                else
                  211
              else
                if a.val < 165 then
                  212
                else
                  213
            else
              if a.val < 168 then
                if a.val < 167 then
                  214
                else
                  215
              else
                if a.val < 169 then
                  216
                else
                  if a.val < 170 then
                    217
                  else
                    218
          else
            if a.val < 175 then
              if a.val < 173 then
                if a.val < 172 then
                  219
                else
                  220
              else
                if a.val < 174 then
                  221
                else
                  222
            else
              if a.val < 177 then
                if a.val < 176 then
                  223
                else
                  96
              else
                if a.val < 178 then
                  97
                else
                  if a.val < 179 then
                    98
                  else
                    99
      else
        if a.val < 198 then
          if a.val < 189 then
            if a.val < 184 then
              if a.val < 182 then
                if a.val < 181 then
                  100
                else
                  101
              else
                if a.val < 183 then
                  102
                else
                  103
            else
              if a.val < 186 then
                if a.val < 185 then
                  104
                else
                  105
              else
                if a.val < 187 then
                  106
                else
                  if a.val < 188 then
                    107
                  else
                    108
          else
            if a.val < 193 then
              if a.val < 191 then
                if a.val < 190 then
                  109
                else
                  110
              else
                if a.val < 192 then
                  111
                else
                  128
            else
              if a.val < 195 then
                if a.val < 194 then
                  129
                else
                  130
              else
                if a.val < 196 then
                  131
                else
                  if a.val < 197 then
                    132
                  else
                    133
        else
          if a.val < 207 then
            if a.val < 202 then
              if a.val < 200 then
                if a.val < 199 then
                  134
                else
                  135
              else
                if a.val < 201 then
                  136
                else
                  137
            else
              if a.val < 204 then
                if a.val < 203 then
                  138
                else
                  139
              else
                if a.val < 205 then
                  140
                else
                  if a.val < 206 then
                    141
                  else
                    142
          else
            if a.val < 211 then
              if a.val < 209 then
                if a.val < 208 then
                  143
                else
                  160
              else
                if a.val < 210 then
                  161
                else
                  162
            else
              if a.val < 213 then
                if a.val < 212 then
                  163
                else
                  164
              else
                if a.val < 214 then
                  165
                else
                  if a.val < 215 then
                    166
                  else
                    167
    else
      if a.val < 252 then
        if a.val < 234 then
          if a.val < 225 then
            if a.val < 220 then
              if a.val < 218 then
                if a.val < 217 then
                  168
                else
                  169
              else
                if a.val < 219 then
                  170
                else
                  171
            else
              if a.val < 222 then
                if a.val < 221 then
                  172
                else
                  173
              else
                if a.val < 223 then
                  174
                else
                  if a.val < 224 then
                    175
                  else
                    225
          else
            if a.val < 229 then
              if a.val < 227 then
                if a.val < 226 then
                  224
                else
                  227
              else
                if a.val < 228 then
                  226
                else
                  229
            else
              if a.val < 231 then
                if a.val < 230 then
                  228
                else
                  231
              else
                if a.val < 232 then
                  230
                else
                  if a.val < 233 then
                    233
                  else
                    232
        else
          if a.val < 243 then
            if a.val < 238 then
              if a.val < 236 then
                if a.val < 235 then
                  235
                else
                  234
              else
                if a.val < 237 then
                  237
                else
                  236
            else
              if a.val < 240 then
                if a.val < 239 then
                  239
                else
                  238
              else
                if a.val < 241 then
                  271
                else
                  if a.val < 242 then
                    269
                  else
                    270
          else
            if a.val < 247 then
              if a.val < 245 then
                if a.val < 244 then
                  268
                else
                  264
              else
                if a.val < 246 then
                  266
                else
                  265
            else
              if a.val < 249 then
                if a.val < 248 then
                  267
                else
                  272
              else
                if a.val < 250 then
                  273
                else
                  if a.val < 251 then
                    274
                  else
                    275
      else
        if a.val < 270 then
          if a.val < 261 then
            if a.val < 256 then
              if a.val < 254 then
                if a.val < 253 then
                  276
                else
                  277
              else
                if a.val < 255 then
                  278
                else
                  279
            else
              if a.val < 258 then
                if a.val < 257 then
                  280
                else
                  281
              else
                if a.val < 259 then
                  282
                else
                  if a.val < 260 then
                    283
                  else
                    284
          else
            if a.val < 265 then
              if a.val < 263 then
                if a.val < 262 then
                  285
                else
                  286
              else
                if a.val < 264 then
                  287
                else
                  244
            else
              if a.val < 267 then
                if a.val < 266 then
                  246
                else
                  245
              else
                if a.val < 268 then
                  247
                else
                  if a.val < 269 then
                    243
                  else
                    241
        else
          if a.val < 279 then
            if a.val < 274 then
              if a.val < 272 then
                if a.val < 271 then
                  242
                else
                  240
              else
                if a.val < 273 then
                  248
                else
                  249
            else
              if a.val < 276 then
                if a.val < 275 then
                  250
                else
                  251
              else
                if a.val < 277 then
                  252
                else
                  if a.val < 278 then
                    253
                  else
                    254
          else
            if a.val < 283 then
              if a.val < 281 then
                if a.val < 280 then
                  255
                else
                  256
              else
                if a.val < 282 then
                  257
                else
                  258
            else
              if a.val < 285 then
                if a.val < 284 then
                  259
                else
                  260
              else
                if a.val < 286 then
                  261
                else
                  if a.val < 287 then
                    262
                  else
                    263

def swap12Phase (a : Fin 288) : Fin 4 :=
  if a.val < 144 then
    0
  else
    if a.val < 216 then
      0
    else
      if a.val < 252 then
        if a.val < 234 then
          0
        else
          if a.val < 243 then
            if a.val < 238 then
              0
            else
              if a.val < 240 then
                0
              else
                3
          else
            if a.val < 247 then
              3
            else
              if a.val < 249 then
                if a.val < 248 then
                  3
                else
                  0
              else
                0
      else
        if a.val < 270 then
          if a.val < 261 then
            0
          else
            if a.val < 265 then
              if a.val < 263 then
                0
              else
                if a.val < 264 then
                  0
                else
                  1
            else
              1
        else
          if a.val < 279 then
            if a.val < 274 then
              if a.val < 272 then
                1
              else
                0
            else
              0
          else
            0

def swap13Index (a : Fin 288) : Fin 288 :=
  if a.val < 144 then
    if a.val < 72 then
      if a.val < 36 then
        if a.val < 18 then
          if a.val < 9 then
            if a.val < 4 then
              if a.val < 2 then
                if a.val < 1 then
                  17
                else
                  16
              else
                if a.val < 3 then
                  19
                else
                  18
            else
              if a.val < 6 then
                if a.val < 5 then
                  21
                else
                  20
              else
                if a.val < 7 then
                  23
                else
                  if a.val < 8 then
                    22
                  else
                    9
          else
            if a.val < 13 then
              if a.val < 11 then
                if a.val < 10 then
                  8
                else
                  11
              else
                if a.val < 12 then
                  10
                else
                  13
            else
              if a.val < 15 then
                if a.val < 14 then
                  12
                else
                  15
              else
                if a.val < 16 then
                  14
                else
                  if a.val < 17 then
                    1
                  else
                    0
        else
          if a.val < 27 then
            if a.val < 22 then
              if a.val < 20 then
                if a.val < 19 then
                  3
                else
                  2
              else
                if a.val < 21 then
                  5
                else
                  4
            else
              if a.val < 24 then
                if a.val < 23 then
                  7
                else
                  6
              else
                if a.val < 25 then
                  41
                else
                  if a.val < 26 then
                    40
                  else
                    43
          else
            if a.val < 31 then
              if a.val < 29 then
                if a.val < 28 then
                  42
                else
                  45
              else
                if a.val < 30 then
                  44
                else
                  47
            else
              if a.val < 33 then
                if a.val < 32 then
                  46
                else
                  33
              else
                if a.val < 34 then
                  32
                else
                  if a.val < 35 then
                    35
                  else
                    34
      else
        if a.val < 54 then
          if a.val < 45 then
            if a.val < 40 then
              if a.val < 38 then
                if a.val < 37 then
                  37
                else
                  36
              else
                if a.val < 39 then
                  39
                else
                  38
            else
              if a.val < 42 then
                if a.val < 41 then
                  25
                else
                  24
              else
                if a.val < 43 then
                  27
                else
                  if a.val < 44 then
                    26
                  else
                    29
          else
            if a.val < 49 then
              if a.val < 47 then
                if a.val < 46 then
                  28
                else
                  31
              else
                if a.val < 48 then
                  30
                else
                  113
            else
              if a.val < 51 then
                if a.val < 50 then
                  112
                else
                  115
              else
                if a.val < 52 then
                  114
                else
                  if a.val < 53 then
                    117
                  else
                    116
        else
          if a.val < 63 then
            if a.val < 58 then
              if a.val < 56 then
                if a.val < 55 then
                  119
                else
                  118
              else
                if a.val < 57 then
                  145
                else
                  144
            else
              if a.val < 60 then
                if a.val < 59 then
                  147
                else
                  146
              else
                if a.val < 61 then
                  149
                else
                  if a.val < 62 then
                    148
                  else
                    151
          else
            if a.val < 67 then
              if a.val < 65 then
                if a.val < 64 then
                  150
                else
                  65
              else
                if a.val < 66 then
                  64
                else
                  67
            else
              if a.val < 69 then
                if a.val < 68 then
                  66
                else
                  69
              else
                if a.val < 70 then
                  68
                else
                  if a.val < 71 then
                    71
                  else
                    70
    else
      if a.val < 108 then
        if a.val < 90 then
          if a.val < 81 then
            if a.val < 76 then
              if a.val < 74 then
                if a.val < 73 then
                  192
                else
                  193
              else
                if a.val < 75 then
                  194
                else
                  195
            else
              if a.val < 78 then
                if a.val < 77 then
                  196
                else
                  197
              else
                if a.val < 79 then
                  198
                else
                  if a.val < 80 then
                    199
                  else
                    81
          else
            if a.val < 85 then
              if a.val < 83 then
                if a.val < 82 then
                  80
                else
                  83
              else
                if a.val < 84 then
                  82
                else
                  85
            else
              if a.val < 87 then
                if a.val < 86 then
                  84
                else
                  87
              else
                if a.val < 88 then
                  86
                else
                  if a.val < 89 then
                    208
                  else
                    209
        else
          if a.val < 99 then
            if a.val < 94 then
              if a.val < 92 then
                if a.val < 91 then
                  210
                else
                  211
              else
                if a.val < 93 then
                  212
                else
                  213
            else
              if a.val < 96 then
                if a.val < 95 then
                  214
                else
                  215
              else
                if a.val < 97 then
                  128
                else
                  if a.val < 98 then
                    129
                  else
                    130
          else
            if a.val < 103 then
              if a.val < 101 then
                if a.val < 100 then
                  131
                else
                  132
              else
                if a.val < 102 then
                  133
                else
                  134
            else
              if a.val < 105 then
                if a.val < 104 then
                  135
                else
                  160
              else
                if a.val < 106 then
                  161
                else
                  if a.val < 107 then
                    162
                  else
                    163
      else
        if a.val < 126 then
          if a.val < 117 then
            if a.val < 112 then
              if a.val < 110 then
                if a.val < 109 then
                  164
                else
                  165
              else
                if a.val < 111 then
                  166
                else
                  167
            else
              if a.val < 114 then
                if a.val < 113 then
                  49
                else
                  48
              else
                if a.val < 115 then
                  51
                else
                  if a.val < 116 then
                    50
                  else
                    53
          else
            if a.val < 121 then
              if a.val < 119 then
                if a.val < 118 then
                  52
                else
                  55
              else
                if a.val < 120 then
                  54
                else
                  176
            else
              if a.val < 123 then
                if a.val < 122 then
                  177
                else
                  178
              else
                if a.val < 124 then
                  179
                else
                  if a.val < 125 then
                    180
                  else
                    181
        else
          if a.val < 135 then
            if a.val < 130 then
              if a.val < 128 then
                if a.val < 127 then
                  182
                else
                  183
              else
                if a.val < 129 then
                  96
                else
                  97
            else
              if a.val < 132 then
                if a.val < 131 then
                  98
                else
                  99
              else
                if a.val < 133 then
                  100
                else
                  if a.val < 134 then
                    101
                  else
                    102
          else
            if a.val < 139 then
              if a.val < 137 then
                if a.val < 136 then
                  103
                else
                  225
              else
                if a.val < 138 then
                  224
                else
                  227
            else
              if a.val < 141 then
                if a.val < 140 then
                  226
                else
                  229
              else
                if a.val < 142 then
                  228
                else
                  if a.val < 143 then
                    231
                  else
                    230
  else
    if a.val < 216 then
      if a.val < 180 then
        if a.val < 162 then
          if a.val < 153 then
            if a.val < 148 then
              if a.val < 146 then
                if a.val < 145 then
                  57
                else
                  56
              else
                if a.val < 147 then
                  59
                else
                  58
            else
              if a.val < 150 then
                if a.val < 149 then
                  61
                else
                  60
              else
                if a.val < 151 then
                  63
                else
                  if a.val < 152 then
                    62
                  else
                    184
          else
            if a.val < 157 then
              if a.val < 155 then
                if a.val < 154 then
                  185
                else
                  186
              else
                if a.val < 156 then
                  187
                else
                  188
            else
              if a.val < 159 then
                if a.val < 158 then
                  189
                else
                  190
              else
                if a.val < 160 then
                  191
                else
                  if a.val < 161 then
                    104
                  else
                    105
        else
          if a.val < 171 then
            if a.val < 166 then
              if a.val < 164 then
                if a.val < 163 then
                  106
                else
                  107
              else
                if a.val < 165 then
                  108
                else
                  109
            else
              if a.val < 168 then
                if a.val < 167 then
                  110
                else
                  111
              else
                if a.val < 169 then
                  233
                else
                  if a.val < 170 then
                    232
                  else
                    235
          else
            if a.val < 175 then
              if a.val < 173 then
                if a.val < 172 then
                  234
                else
                  237
              else
                if a.val < 174 then
                  236
                else
                  239
            else
              if a.val < 177 then
                if a.val < 176 then
                  238
                else
                  120
              else
                if a.val < 178 then
                  121
                else
                  if a.val < 179 then
                    122
                  else
                    123
      else
        if a.val < 198 then
          if a.val < 189 then
            if a.val < 184 then
              if a.val < 182 then
                if a.val < 181 then
                  124
                else
                  125
              else
                if a.val < 183 then
                  126
                else
                  127
            else
              if a.val < 186 then
                if a.val < 185 then
                  152
                else
                  153
              else
                if a.val < 187 then
                  154
                else
                  if a.val < 188 then
                    155
                  else
                    156
          else
            if a.val < 193 then
              if a.val < 191 then
                if a.val < 190 then
                  157
                else
                  158
              else
                if a.val < 192 then
                  159
                else
                  72
            else
              if a.val < 195 then
                if a.val < 194 then
                  73
                else
                  74
              else
                if a.val < 196 then
                  75
                else
                  if a.val < 197 then
                    76
                  else
                    77
        else
          if a.val < 207 then
            if a.val < 202 then
              if a.val < 200 then
                if a.val < 199 then
                  78
                else
                  79
              else
                if a.val < 201 then
                  201
                else
                  200
            else
              if a.val < 204 then
                if a.val < 203 then
                  203
                else
                  202
              else
                if a.val < 205 then
                  205
                else
                  if a.val < 206 then
                    204
                  else
                    207
          else
            if a.val < 211 then
              if a.val < 209 then
                if a.val < 208 then
                  206
                else
                  88
              else
                if a.val < 210 then
                  89
                else
                  90
            else
              if a.val < 213 then
                if a.val < 212 then
                  91
                else
                  92
              else
                if a.val < 214 then
                  93
                else
                  if a.val < 215 then
                    94
                  else
                    95
    else
      if a.val < 252 then
        if a.val < 234 then
          if a.val < 225 then
            if a.val < 220 then
              if a.val < 218 then
                if a.val < 217 then
                  217
                else
                  216
              else
                if a.val < 219 then
                  219
                else
                  218
            else
              if a.val < 222 then
                if a.val < 221 then
                  221
                else
                  220
              else
                if a.val < 223 then
                  223
                else
                  if a.val < 224 then
                    222
                  else
                    137
          else
            if a.val < 229 then
              if a.val < 227 then
                if a.val < 226 then
                  136
                else
                  139
              else
                if a.val < 228 then
                  138
                else
                  141
            else
              if a.val < 231 then
                if a.val < 230 then
                  140
                else
                  143
              else
                if a.val < 232 then
                  142
                else
                  if a.val < 233 then
                    169
                  else
                    168
        else
          if a.val < 243 then
            if a.val < 238 then
              if a.val < 236 then
                if a.val < 235 then
                  171
                else
                  170
              else
                if a.val < 237 then
                  173
                else
                  172
            else
              if a.val < 240 then
                if a.val < 239 then
                  175
                else
                  174
              else
                if a.val < 241 then
                  287
                else
                  if a.val < 242 then
                    285
                  else
                    286
          else
            if a.val < 247 then
              if a.val < 245 then
                if a.val < 244 then
                  284
                else
                  280
              else
                if a.val < 246 then
                  282
                else
                  281
            else
              if a.val < 249 then
                if a.val < 248 then
                  283
                else
                  263
              else
                if a.val < 250 then
                  261
                else
                  if a.val < 251 then
                    262
                  else
                    260
      else
        if a.val < 270 then
          if a.val < 261 then
            if a.val < 256 then
              if a.val < 254 then
                if a.val < 253 then
                  256
                else
                  258
              else
                if a.val < 255 then
                  257
                else
                  259
            else
              if a.val < 258 then
                if a.val < 257 then
                  252
                else
                  254
              else
                if a.val < 259 then
                  253
                else
                  if a.val < 260 then
                    255
                  else
                    251
          else
            if a.val < 265 then
              if a.val < 263 then
                if a.val < 262 then
                  249
                else
                  250
              else
                if a.val < 264 then
                  248
                else
                  276
            else
              if a.val < 267 then
                if a.val < 266 then
                  278
                else
                  277
              else
                if a.val < 268 then
                  279
                else
                  if a.val < 269 then
                    275
                  else
                    273
        else
          if a.val < 279 then
            if a.val < 274 then
              if a.val < 272 then
                if a.val < 271 then
                  274
                else
                  272
              else
                if a.val < 273 then
                  271
                else
                  269
            else
              if a.val < 276 then
                if a.val < 275 then
                  270
                else
                  268
              else
                if a.val < 277 then
                  264
                else
                  if a.val < 278 then
                    266
                  else
                    265
          else
            if a.val < 283 then
              if a.val < 281 then
                if a.val < 280 then
                  267
                else
                  244
              else
                if a.val < 282 then
                  246
                else
                  245
            else
              if a.val < 285 then
                if a.val < 284 then
                  247
                else
                  243
              else
                if a.val < 286 then
                  241
                else
                  if a.val < 287 then
                    242
                  else
                    240

def swap13Phase (a : Fin 288) : Fin 4 :=
  if a.val < 144 then
    0
  else
    if a.val < 216 then
      0
    else
      if a.val < 252 then
        if a.val < 234 then
          0
        else
          if a.val < 243 then
            if a.val < 238 then
              0
            else
              if a.val < 240 then
                0
              else
                3
          else
            3
      else
        if a.val < 270 then
          if a.val < 261 then
            if a.val < 256 then
              3
            else
              1
          else
            1
        else
          if a.val < 279 then
            if a.val < 274 then
              if a.val < 272 then
                1
              else
                3
            else
              3
          else
            if a.val < 283 then
              if a.val < 281 then
                if a.val < 280 then
                  3
                else
                  1
              else
                1
            else
              1

def swap23Index (a : Fin 288) : Fin 288 :=
  if a.val < 144 then
    if a.val < 72 then
      if a.val < 36 then
        if a.val < 18 then
          if a.val < 9 then
            if a.val < 4 then
              if a.val < 2 then
                if a.val < 1 then
                  1
                else
                  0
              else
                if a.val < 3 then
                  3
                else
                  2
            else
              if a.val < 6 then
                if a.val < 5 then
                  5
                else
                  4
              else
                if a.val < 7 then
                  7
                else
                  if a.val < 8 then
                    6
                  else
                    16
          else
            if a.val < 13 then
              if a.val < 11 then
                if a.val < 10 then
                  17
                else
                  18
              else
                if a.val < 12 then
                  19
                else
                  20
            else
              if a.val < 15 then
                if a.val < 14 then
                  21
                else
                  22
              else
                if a.val < 16 then
                  23
                else
                  if a.val < 17 then
                    8
                  else
                    9
        else
          if a.val < 27 then
            if a.val < 22 then
              if a.val < 20 then
                if a.val < 19 then
                  10
                else
                  11
              else
                if a.val < 21 then
                  12
                else
                  13
            else
              if a.val < 24 then
                if a.val < 23 then
                  14
                else
                  15
              else
                if a.val < 25 then
                  32
                else
                  if a.val < 26 then
                    33
                  else
                    34
          else
            if a.val < 31 then
              if a.val < 29 then
                if a.val < 28 then
                  35
                else
                  36
              else
                if a.val < 30 then
                  37
                else
                  38
            else
              if a.val < 33 then
                if a.val < 32 then
                  39
                else
                  24
              else
                if a.val < 34 then
                  25
                else
                  if a.val < 35 then
                    26
                  else
                    27
      else
        if a.val < 54 then
          if a.val < 45 then
            if a.val < 40 then
              if a.val < 38 then
                if a.val < 37 then
                  28
                else
                  29
              else
                if a.val < 39 then
                  30
                else
                  31
            else
              if a.val < 42 then
                if a.val < 41 then
                  41
                else
                  40
              else
                if a.val < 43 then
                  43
                else
                  if a.val < 44 then
                    42
                  else
                    45
          else
            if a.val < 49 then
              if a.val < 47 then
                if a.val < 46 then
                  44
                else
                  47
              else
                if a.val < 48 then
                  46
                else
                  64
            else
              if a.val < 51 then
                if a.val < 50 then
                  65
                else
                  66
              else
                if a.val < 52 then
                  67
                else
                  if a.val < 53 then
                    68
                  else
                    69
        else
          if a.val < 63 then
            if a.val < 58 then
              if a.val < 56 then
                if a.val < 55 then
                  70
                else
                  71
              else
                if a.val < 57 then
                  80
                else
                  81
            else
              if a.val < 60 then
                if a.val < 59 then
                  82
                else
                  83
              else
                if a.val < 61 then
                  84
                else
                  if a.val < 62 then
                    85
                  else
                    86
          else
            if a.val < 67 then
              if a.val < 65 then
                if a.val < 64 then
                  87
                else
                  48
              else
                if a.val < 66 then
                  49
                else
                  50
            else
              if a.val < 69 then
                if a.val < 68 then
                  51
                else
                  52
              else
                if a.val < 70 then
                  53
                else
                  if a.val < 71 then
                    54
                  else
                    55
    else
      if a.val < 108 then
        if a.val < 90 then
          if a.val < 81 then
            if a.val < 76 then
              if a.val < 74 then
                if a.val < 73 then
                  96
                else
                  97
              else
                if a.val < 75 then
                  98
                else
                  99
            else
              if a.val < 78 then
                if a.val < 77 then
                  100
                else
                  101
              else
                if a.val < 79 then
                  102
                else
                  if a.val < 80 then
                    103
                  else
                    56
          else
            if a.val < 85 then
              if a.val < 83 then
                if a.val < 82 then
                  57
                else
                  58
              else
                if a.val < 84 then
                  59
                else
                  60
            else
              if a.val < 87 then
                if a.val < 86 then
                  61
                else
                  62
              else
                if a.val < 88 then
                  63
                else
                  if a.val < 89 then
                    104
                  else
                    105
        else
          if a.val < 99 then
            if a.val < 94 then
              if a.val < 92 then
                if a.val < 91 then
                  106
                else
                  107
              else
                if a.val < 93 then
                  108
                else
                  109
            else
              if a.val < 96 then
                if a.val < 95 then
                  110
                else
                  111
              else
                if a.val < 97 then
                  72
                else
                  if a.val < 98 then
                    73
                  else
                    74
          else
            if a.val < 103 then
              if a.val < 101 then
                if a.val < 100 then
                  75
                else
                  76
              else
                if a.val < 102 then
                  77
                else
                  78
            else
              if a.val < 105 then
                if a.val < 104 then
                  79
                else
                  88
              else
                if a.val < 106 then
                  89
                else
                  if a.val < 107 then
                    90
                  else
                    91
      else
        if a.val < 126 then
          if a.val < 117 then
            if a.val < 112 then
              if a.val < 110 then
                if a.val < 109 then
                  92
                else
                  93
              else
                if a.val < 111 then
                  94
                else
                  95
            else
              if a.val < 114 then
                if a.val < 113 then
                  113
                else
                  112
              else
                if a.val < 115 then
                  115
                else
                  if a.val < 116 then
                    114
                  else
                    117
          else
            if a.val < 121 then
              if a.val < 119 then
                if a.val < 118 then
                  116
                else
                  119
              else
                if a.val < 120 then
                  118
                else
                  128
            else
              if a.val < 123 then
                if a.val < 122 then
                  129
                else
                  130
              else
                if a.val < 124 then
                  131
                else
                  if a.val < 125 then
                    132
                  else
                    133
        else
          if a.val < 135 then
            if a.val < 130 then
              if a.val < 128 then
                if a.val < 127 then
                  134
                else
                  135
              else
                if a.val < 129 then
                  120
                else
                  121
            else
              if a.val < 132 then
                if a.val < 131 then
                  122
                else
                  123
              else
                if a.val < 133 then
                  124
                else
                  if a.val < 134 then
                    125
                  else
                    126
          else
            if a.val < 139 then
              if a.val < 137 then
                if a.val < 136 then
                  127
                else
                  137
              else
                if a.val < 138 then
                  136
                else
                  139
            else
              if a.val < 141 then
                if a.val < 140 then
                  138
                else
                  141
              else
                if a.val < 142 then
                  140
                else
                  if a.val < 143 then
                    143
                  else
                    142
  else
    if a.val < 216 then
      if a.val < 180 then
        if a.val < 162 then
          if a.val < 153 then
            if a.val < 148 then
              if a.val < 146 then
                if a.val < 145 then
                  145
                else
                  144
              else
                if a.val < 147 then
                  147
                else
                  146
            else
              if a.val < 150 then
                if a.val < 149 then
                  149
                else
                  148
              else
                if a.val < 151 then
                  151
                else
                  if a.val < 152 then
                    150
                  else
                    160
          else
            if a.val < 157 then
              if a.val < 155 then
                if a.val < 154 then
                  161
                else
                  162
              else
                if a.val < 156 then
                  163
                else
                  164
            else
              if a.val < 159 then
                if a.val < 158 then
                  165
                else
                  166
              else
                if a.val < 160 then
                  167
                else
                  if a.val < 161 then
                    152
                  else
                    153
        else
          if a.val < 171 then
            if a.val < 166 then
              if a.val < 164 then
                if a.val < 163 then
                  154
                else
                  155
              else
                if a.val < 165 then
                  156
                else
                  157
            else
              if a.val < 168 then
                if a.val < 167 then
                  158
                else
                  159
              else
                if a.val < 169 then
                  169
                else
                  if a.val < 170 then
                    168
                  else
                    171
          else
            if a.val < 175 then
              if a.val < 173 then
                if a.val < 172 then
                  170
                else
                  173
              else
                if a.val < 174 then
                  172
                else
                  175
            else
              if a.val < 177 then
                if a.val < 176 then
                  174
                else
                  192
              else
                if a.val < 178 then
                  193
                else
                  if a.val < 179 then
                    194
                  else
                    195
      else
        if a.val < 198 then
          if a.val < 189 then
            if a.val < 184 then
              if a.val < 182 then
                if a.val < 181 then
                  196
                else
                  197
              else
                if a.val < 183 then
                  198
                else
                  199
            else
              if a.val < 186 then
                if a.val < 185 then
                  208
                else
                  209
              else
                if a.val < 187 then
                  210
                else
                  if a.val < 188 then
                    211
                  else
                    212
          else
            if a.val < 193 then
              if a.val < 191 then
                if a.val < 190 then
                  213
                else
                  214
              else
                if a.val < 192 then
                  215
                else
                  176
            else
              if a.val < 195 then
                if a.val < 194 then
                  177
                else
                  178
              else
                if a.val < 196 then
                  179
                else
                  if a.val < 197 then
                    180
                  else
                    181
        else
          if a.val < 207 then
            if a.val < 202 then
              if a.val < 200 then
                if a.val < 199 then
                  182
                else
                  183
              else
                if a.val < 201 then
                  224
                else
                  225
            else
              if a.val < 204 then
                if a.val < 203 then
                  226
                else
                  227
              else
                if a.val < 205 then
                  228
                else
                  if a.val < 206 then
                    229
                  else
                    230
          else
            if a.val < 211 then
              if a.val < 209 then
                if a.val < 208 then
                  231
                else
                  184
              else
                if a.val < 210 then
                  185
                else
                  186
            else
              if a.val < 213 then
                if a.val < 212 then
                  187
                else
                  188
              else
                if a.val < 214 then
                  189
                else
                  if a.val < 215 then
                    190
                  else
                    191
    else
      if a.val < 252 then
        if a.val < 234 then
          if a.val < 225 then
            if a.val < 220 then
              if a.val < 218 then
                if a.val < 217 then
                  232
                else
                  233
              else
                if a.val < 219 then
                  234
                else
                  235
            else
              if a.val < 222 then
                if a.val < 221 then
                  236
                else
                  237
              else
                if a.val < 223 then
                  238
                else
                  if a.val < 224 then
                    239
                  else
                    200
          else
            if a.val < 229 then
              if a.val < 227 then
                if a.val < 226 then
                  201
                else
                  202
              else
                if a.val < 228 then
                  203
                else
                  204
            else
              if a.val < 231 then
                if a.val < 230 then
                  205
                else
                  206
              else
                if a.val < 232 then
                  207
                else
                  if a.val < 233 then
                    216
                  else
                    217
        else
          if a.val < 243 then
            if a.val < 238 then
              if a.val < 236 then
                if a.val < 235 then
                  218
                else
                  219
              else
                if a.val < 237 then
                  220
                else
                  221
            else
              if a.val < 240 then
                if a.val < 239 then
                  222
                else
                  223
              else
                if a.val < 241 then
                  248
                else
                  if a.val < 242 then
                    249
                  else
                    250
          else
            if a.val < 247 then
              if a.val < 245 then
                if a.val < 244 then
                  251
                else
                  252
              else
                if a.val < 246 then
                  253
                else
                  254
            else
              if a.val < 249 then
                if a.val < 248 then
                  255
                else
                  240
              else
                if a.val < 250 then
                  241
                else
                  if a.val < 251 then
                    242
                  else
                    243
      else
        if a.val < 270 then
          if a.val < 261 then
            if a.val < 256 then
              if a.val < 254 then
                if a.val < 253 then
                  244
                else
                  245
              else
                if a.val < 255 then
                  246
                else
                  247
            else
              if a.val < 258 then
                if a.val < 257 then
                  264
                else
                  265
              else
                if a.val < 259 then
                  266
                else
                  if a.val < 260 then
                    267
                  else
                    268
          else
            if a.val < 265 then
              if a.val < 263 then
                if a.val < 262 then
                  269
                else
                  270
              else
                if a.val < 264 then
                  271
                else
                  256
            else
              if a.val < 267 then
                if a.val < 266 then
                  257
                else
                  258
              else
                if a.val < 268 then
                  259
                else
                  if a.val < 269 then
                    260
                  else
                    261
        else
          if a.val < 279 then
            if a.val < 274 then
              if a.val < 272 then
                if a.val < 271 then
                  262
                else
                  263
              else
                if a.val < 273 then
                  287
                else
                  285
            else
              if a.val < 276 then
                if a.val < 275 then
                  286
                else
                  284
              else
                if a.val < 277 then
                  280
                else
                  if a.val < 278 then
                    282
                  else
                    281
          else
            if a.val < 283 then
              if a.val < 281 then
                if a.val < 280 then
                  283
                else
                  276
              else
                if a.val < 282 then
                  278
                else
                  277
            else
              if a.val < 285 then
                if a.val < 284 then
                  279
                else
                  275
              else
                if a.val < 286 then
                  273
                else
                  if a.val < 287 then
                    274
                  else
                    272

def swap23Phase (a : Fin 288) : Fin 4 :=
  if a.val < 144 then
    0
  else
    if a.val < 216 then
      0
    else
      if a.val < 252 then
        0
      else
        if a.val < 270 then
          0
        else
          if a.val < 279 then
            if a.val < 274 then
              if a.val < 272 then
                0
              else
                3
            else
              3
          else
            if a.val < 283 then
              if a.val < 281 then
                if a.val < 280 then
                  3
                else
                  1
              else
                1
            else
              1

def hadamardIndex (a : Fin 288) : Fin 288 :=
  if a.val < 144 then
    if a.val < 72 then
      if a.val < 36 then
        if a.val < 18 then
          if a.val < 9 then
            if a.val < 4 then
              if a.val < 2 then
                if a.val < 1 then
                  200
                else
                  201
              else
                if a.val < 3 then
                  202
                else
                  203
            else
              if a.val < 6 then
                if a.val < 5 then
                  206
                else
                  207
              else
                if a.val < 7 then
                  204
                else
                  if a.val < 8 then
                    205
                  else
                    136
          else
            if a.val < 13 then
              if a.val < 11 then
                if a.val < 10 then
                  137
                else
                  138
              else
                if a.val < 12 then
                  139
                else
                  142
            else
              if a.val < 15 then
                if a.val < 14 then
                  143
                else
                  140
              else
                if a.val < 16 then
                  141
                else
                  if a.val < 17 then
                    225
                  else
                    224
        else
          if a.val < 27 then
            if a.val < 22 then
              if a.val < 20 then
                if a.val < 19 then
                  227
                else
                  226
              else
                if a.val < 21 then
                  231
                else
                  230
            else
              if a.val < 24 then
                if a.val < 23 then
                  229
                else
                  228
              else
                if a.val < 25 then
                  55
                else
                  if a.val < 26 then
                    54
                  else
                    53
          else
            if a.val < 31 then
              if a.val < 29 then
                if a.val < 28 then
                  52
                else
                  50
              else
                if a.val < 30 then
                  51
                else
                  48
            else
              if a.val < 33 then
                if a.val < 32 then
                  49
                else
                  118
              else
                if a.val < 34 then
                  119
                else
                  if a.val < 35 then
                    116
                  else
                    117
      else
        if a.val < 54 then
          if a.val < 45 then
            if a.val < 40 then
              if a.val < 38 then
                if a.val < 37 then
                  115
                else
                  114
              else
                if a.val < 39 then
                  113
                else
                  112
            else
              if a.val < 42 then
                if a.val < 41 then
                  70
                else
                  71
              else
                if a.val < 43 then
                  68
                else
                  if a.val < 44 then
                    69
                  else
                    67
          else
            if a.val < 49 then
              if a.val < 47 then
                if a.val < 46 then
                  66
                else
                  65
              else
                if a.val < 48 then
                  64
                else
                  30
            else
              if a.val < 51 then
                if a.val < 50 then
                  31
                else
                  28
              else
                if a.val < 52 then
                  29
                else
                  if a.val < 53 then
                    27
                  else
                    26
        else
          if a.val < 63 then
            if a.val < 58 then
              if a.val < 56 then
                if a.val < 55 then
                  25
                else
                  24
              else
                if a.val < 57 then
                  236
                else
                  237
            else
              if a.val < 60 then
                if a.val < 59 then
                  238
                else
                  239
              else
                if a.val < 61 then
                  235
                else
                  if a.val < 62 then
                    234
                  else
                    233
          else
            if a.val < 67 then
              if a.val < 65 then
                if a.val < 64 then
                  232
                else
                  47
              else
                if a.val < 66 then
                  46
                else
                  45
            else
              if a.val < 69 then
                if a.val < 68 then
                  44
                else
                  42
              else
                if a.val < 70 then
                  43
                else
                  if a.val < 71 then
                    40
                  else
                    41
    else
      if a.val < 108 then
        if a.val < 90 then
          if a.val < 81 then
            if a.val < 76 then
              if a.val < 74 then
                if a.val < 73 then
                  120
                else
                  122
              else
                if a.val < 75 then
                  121
                else
                  123
            else
              if a.val < 78 then
                if a.val < 77 then
                  127
                else
                  125
              else
                if a.val < 79 then
                  126
                else
                  if a.val < 80 then
                    124
                  else
                    173
          else
            if a.val < 85 then
              if a.val < 83 then
                if a.val < 82 then
                  172
                else
                  175
              else
                if a.val < 84 then
                  174
                else
                  170
            else
              if a.val < 87 then
                if a.val < 86 then
                  171
                else
                  168
              else
                if a.val < 88 then
                  169
                else
                  if a.val < 89 then
                    284
                  else
                    285
        else
          if a.val < 99 then
            if a.val < 94 then
              if a.val < 92 then
                if a.val < 91 then
                  286
                else
                  287
              else
                if a.val < 93 then
                  282
                else
                  280
            else
              if a.val < 96 then
                if a.val < 95 then
                  283
                else
                  281
              else
                if a.val < 97 then
                  176
                else
                  if a.val < 98 then
                    178
                  else
                    177
          else
            if a.val < 103 then
              if a.val < 101 then
                if a.val < 100 then
                  179
                else
                  183
              else
                if a.val < 102 then
                  181
                else
                  182
            else
              if a.val < 105 then
                if a.val < 104 then
                  180
                else
                  243
              else
                if a.val < 106 then
                  241
                else
                  if a.val < 107 then
                    242
                  else
                    240
      else
        if a.val < 126 then
          if a.val < 117 then
            if a.val < 112 then
              if a.val < 110 then
                if a.val < 109 then
                  245
                else
                  244
              else
                if a.val < 111 then
                  247
                else
                  246
            else
              if a.val < 114 then
                if a.val < 113 then
                  39
                else
                  38
              else
                if a.val < 115 then
                  37
                else
                  if a.val < 116 then
                    36
                  else
                    34
          else
            if a.val < 121 then
              if a.val < 119 then
                if a.val < 118 then
                  35
                else
                  32
              else
                if a.val < 120 then
                  33
                else
                  72
            else
              if a.val < 123 then
                if a.val < 122 then
                  74
                else
                  73
              else
                if a.val < 124 then
                  75
                else
                  if a.val < 125 then
                    79
                  else
                    77
        else
          if a.val < 135 then
            if a.val < 130 then
              if a.val < 128 then
                if a.val < 127 then
                  78
                else
                  76
              else
                if a.val < 129 then
                  192
                else
                  194
            else
              if a.val < 132 then
                if a.val < 131 then
                  193
                else
                  195
              else
                if a.val < 133 then
                  199
                else
                  if a.val < 134 then
                    197
                  else
                    198
          else
            if a.val < 139 then
              if a.val < 137 then
                if a.val < 136 then
                  196
                else
                  8
              else
                if a.val < 138 then
                  9
                else
                  10
            else
              if a.val < 141 then
                if a.val < 140 then
                  11
                else
                  14
              else
                if a.val < 142 then
                  15
                else
                  if a.val < 143 then
                    12
                  else
                    13
  else
    if a.val < 216 then
      if a.val < 180 then
        if a.val < 162 then
          if a.val < 153 then
            if a.val < 148 then
              if a.val < 146 then
                if a.val < 145 then
                  221
                else
                  220
              else
                if a.val < 147 then
                  223
                else
                  222
            else
              if a.val < 150 then
                if a.val < 149 then
                  218
                else
                  219
              else
                if a.val < 151 then
                  216
                else
                  if a.val < 152 then
                    217
                  else
                    260
          else
            if a.val < 157 then
              if a.val < 155 then
                if a.val < 154 then
                  261
                else
                  262
              else
                if a.val < 156 then
                  263
                else
                  258
            else
              if a.val < 159 then
                if a.val < 158 then
                  256
                else
                  259
              else
                if a.val < 160 then
                  257
                else
                  if a.val < 161 then
                    251
                  else
                    249
        else
          if a.val < 171 then
            if a.val < 166 then
              if a.val < 164 then
                if a.val < 163 then
                  250
                else
                  248
              else
                if a.val < 165 then
                  253
                else
                  252
            else
              if a.val < 168 then
                if a.val < 167 then
                  255
                else
                  254
              else
                if a.val < 169 then
                  86
                else
                  if a.val < 170 then
                    87
                  else
                    84
          else
            if a.val < 175 then
              if a.val < 173 then
                if a.val < 172 then
                  85
                else
                  81
              else
                if a.val < 174 then
                  80
                else
                  83
            else
              if a.val < 177 then
                if a.val < 176 then
                  82
                else
                  96
              else
                if a.val < 178 then
                  98
                else
                  if a.val < 179 then
                    97
                  else
                    99
      else
        if a.val < 198 then
          if a.val < 189 then
            if a.val < 184 then
              if a.val < 182 then
                if a.val < 181 then
                  103
                else
                  101
              else
                if a.val < 183 then
                  102
                else
                  100
            else
              if a.val < 186 then
                if a.val < 185 then
                  268
                else
                  269
              else
                if a.val < 187 then
                  270
                else
                  if a.val < 188 then
                    271
                  else
                    266
          else
            if a.val < 193 then
              if a.val < 191 then
                if a.val < 190 then
                  264
                else
                  267
              else
                if a.val < 192 then
                  265
                else
                  128
            else
              if a.val < 195 then
                if a.val < 194 then
                  130
                else
                  129
              else
                if a.val < 196 then
                  131
                else
                  if a.val < 197 then
                    135
                  else
                    133
        else
          if a.val < 207 then
            if a.val < 202 then
              if a.val < 200 then
                if a.val < 199 then
                  134
                else
                  132
              else
                if a.val < 201 then
                  0
                else
                  1
            else
              if a.val < 204 then
                if a.val < 203 then
                  2
                else
                  3
              else
                if a.val < 205 then
                  6
                else
                  if a.val < 206 then
                    7
                  else
                    4
          else
            if a.val < 211 then
              if a.val < 209 then
                if a.val < 208 then
                  5
                else
                  275
              else
                if a.val < 210 then
                  273
                else
                  274
            else
              if a.val < 213 then
                if a.val < 212 then
                  272
                else
                  277
              else
                if a.val < 214 then
                  276
                else
                  if a.val < 215 then
                    279
                  else
                    278
    else
      if a.val < 252 then
        if a.val < 234 then
          if a.val < 225 then
            if a.val < 220 then
              if a.val < 218 then
                if a.val < 217 then
                  150
                else
                  151
              else
                if a.val < 219 then
                  148
                else
                  149
            else
              if a.val < 222 then
                if a.val < 221 then
                  145
                else
                  144
              else
                if a.val < 223 then
                  147
                else
                  if a.val < 224 then
                    146
                  else
                    17
          else
            if a.val < 229 then
              if a.val < 227 then
                if a.val < 226 then
                  16
                else
                  19
              else
                if a.val < 228 then
                  18
                else
                  23
            else
              if a.val < 231 then
                if a.val < 230 then
                  22
                else
                  21
              else
                if a.val < 232 then
                  20
                else
                  if a.val < 233 then
                    63
                  else
                    62
        else
          if a.val < 243 then
            if a.val < 238 then
              if a.val < 236 then
                if a.val < 235 then
                  61
                else
                  60
              else
                if a.val < 237 then
                  56
                else
                  57
            else
              if a.val < 240 then
                if a.val < 239 then
                  58
                else
                  59
              else
                if a.val < 241 then
                  107
                else
                  if a.val < 242 then
                    105
                  else
                    106
          else
            if a.val < 247 then
              if a.val < 245 then
                if a.val < 244 then
                  104
                else
                  109
              else
                if a.val < 246 then
                  108
                else
                  111
            else
              if a.val < 249 then
                if a.val < 248 then
                  110
                else
                  163
              else
                if a.val < 250 then
                  161
                else
                  if a.val < 251 then
                    162
                  else
                    160
      else
        if a.val < 270 then
          if a.val < 261 then
            if a.val < 256 then
              if a.val < 254 then
                if a.val < 253 then
                  165
                else
                  164
              else
                if a.val < 255 then
                  167
                else
                  166
            else
              if a.val < 258 then
                if a.val < 257 then
                  157
                else
                  159
              else
                if a.val < 259 then
                  156
                else
                  if a.val < 260 then
                    158
                  else
                    152
          else
            if a.val < 265 then
              if a.val < 263 then
                if a.val < 262 then
                  153
                else
                  154
              else
                if a.val < 264 then
                  155
                else
                  189
            else
              if a.val < 267 then
                if a.val < 266 then
                  191
                else
                  188
              else
                if a.val < 268 then
                  190
                else
                  if a.val < 269 then
                    184
                  else
                    185
        else
          if a.val < 279 then
            if a.val < 274 then
              if a.val < 272 then
                if a.val < 271 then
                  186
                else
                  187
              else
                if a.val < 273 then
                  211
                else
                  209
            else
              if a.val < 276 then
                if a.val < 275 then
                  210
                else
                  208
              else
                if a.val < 277 then
                  213
                else
                  if a.val < 278 then
                    212
                  else
                    215
          else
            if a.val < 283 then
              if a.val < 281 then
                if a.val < 280 then
                  214
                else
                  93
              else
                if a.val < 282 then
                  95
                else
                  92
            else
              if a.val < 285 then
                if a.val < 284 then
                  94
                else
                  88
              else
                if a.val < 286 then
                  89
                else
                  if a.val < 287 then
                    90
                  else
                    91

def hadamardPhase (a : Fin 288) : Fin 4 :=
  if a.val < 144 then
    if a.val < 72 then
      if a.val < 36 then
        if a.val < 18 then
          0
        else
          if a.val < 27 then
            if a.val < 22 then
              0
            else
              if a.val < 24 then
                0
              else
                1
          else
            1
      else
        if a.val < 54 then
          if a.val < 45 then
            1
          else
            if a.val < 49 then
              if a.val < 47 then
                1
              else
                if a.val < 48 then
                  1
                else
                  3
            else
              3
        else
          3
    else
      if a.val < 108 then
        if a.val < 90 then
          if a.val < 81 then
            if a.val < 76 then
              0
            else
              if a.val < 78 then
                0
              else
                if a.val < 79 then
                  0
                else
                  if a.val < 80 then
                    0
                  else
                    3
          else
            if a.val < 85 then
              3
            else
              if a.val < 87 then
                3
              else
                if a.val < 88 then
                  3
                else
                  0
        else
          if a.val < 99 then
            0
          else
            if a.val < 103 then
              0
            else
              if a.val < 105 then
                if a.val < 104 then
                  0
                else
                  1
              else
                1
      else
        if a.val < 126 then
          if a.val < 117 then
            if a.val < 112 then
              1
            else
              3
          else
            if a.val < 121 then
              if a.val < 119 then
                3
              else
                if a.val < 120 then
                  3
                else
                  0
            else
              0
        else
          0
  else
    if a.val < 216 then
      if a.val < 180 then
        if a.val < 162 then
          if a.val < 153 then
            if a.val < 148 then
              3
            else
              if a.val < 150 then
                3
              else
                if a.val < 151 then
                  3
                else
                  if a.val < 152 then
                    3
                  else
                    0
          else
            if a.val < 157 then
              0
            else
              if a.val < 159 then
                0
              else
                if a.val < 160 then
                  0
                else
                  1
        else
          if a.val < 171 then
            1
          else
            if a.val < 175 then
              1
            else
              if a.val < 177 then
                if a.val < 176 then
                  1
                else
                  0
              else
                0
      else
        if a.val < 198 then
          0
        else
          if a.val < 207 then
            0
          else
            if a.val < 211 then
              if a.val < 209 then
                if a.val < 208 then
                  0
                else
                  1
              else
                1
            else
              1
    else
      if a.val < 252 then
        if a.val < 234 then
          if a.val < 225 then
            if a.val < 220 then
              1
            else
              if a.val < 222 then
                1
              else
                if a.val < 223 then
                  1
                else
                  if a.val < 224 then
                    1
                  else
                    0
          else
            if a.val < 229 then
              0
            else
              if a.val < 231 then
                0
              else
                if a.val < 232 then
                  0
                else
                  1
        else
          if a.val < 243 then
            if a.val < 238 then
              1
            else
              if a.val < 240 then
                1
              else
                3
          else
            3
      else
        if a.val < 270 then
          if a.val < 261 then
            if a.val < 256 then
              3
            else
              0
          else
            0
        else
          if a.val < 279 then
            if a.val < 274 then
              if a.val < 272 then
                0
              else
                3
            else
              3
          else
            if a.val < 283 then
              if a.val < 281 then
                if a.val < 280 then
                  3
                else
                  0
              else
                0
            else
              0

def swapIndex (m : Fin 6) : Fin 288 → Fin 288 :=
  ![swap01Index,swap02Index,swap03Index,swap12Index,swap13Index,swap23Index] m

def swapPhase (m : Fin 6) : Fin 288 → Fin 4 :=
  ![swap01Phase,swap02Phase,swap03Phase,swap12Phase,swap13Phase,swap23Phase] m

def gramPositive (a : Fin 288) : Bool :=
  if a.val < 144 then
    if a.val < 72 then
      if a.val < 36 then
        if a.val < 18 then
          if a.val < 9 then
            if a.val < 4 then
              true
            else
              if a.val < 6 then
                false
              else
                if a.val < 7 then
                  false
                else
                  if a.val < 8 then
                    false
                  else
                    true
          else
            if a.val < 13 then
              if a.val < 11 then
                true
              else
                if a.val < 12 then
                  true
                else
                  false
            else
              if a.val < 15 then
                false
              else
                if a.val < 16 then
                  false
                else
                  true
        else
          if a.val < 27 then
            if a.val < 22 then
              if a.val < 20 then
                true
              else
                false
            else
              if a.val < 24 then
                false
              else
                true
          else
            if a.val < 31 then
              if a.val < 29 then
                if a.val < 28 then
                  true
                else
                  false
              else
                false
            else
              if a.val < 33 then
                if a.val < 32 then
                  false
                else
                  true
              else
                true
      else
        if a.val < 54 then
          if a.val < 45 then
            if a.val < 40 then
              false
            else
              if a.val < 42 then
                true
              else
                if a.val < 43 then
                  true
                else
                  if a.val < 44 then
                    true
                  else
                    false
          else
            if a.val < 49 then
              if a.val < 47 then
                false
              else
                if a.val < 48 then
                  false
                else
                  true
            else
              if a.val < 51 then
                true
              else
                if a.val < 52 then
                  true
                else
                  false
        else
          if a.val < 63 then
            if a.val < 58 then
              if a.val < 56 then
                false
              else
                true
            else
              if a.val < 60 then
                true
              else
                false
          else
            if a.val < 67 then
              if a.val < 65 then
                if a.val < 64 then
                  false
                else
                  true
              else
                true
            else
              if a.val < 69 then
                if a.val < 68 then
                  true
                else
                  false
              else
                false
    else
      if a.val < 108 then
        if a.val < 90 then
          if a.val < 81 then
            if a.val < 76 then
              true
            else
              if a.val < 78 then
                false
              else
                if a.val < 79 then
                  false
                else
                  if a.val < 80 then
                    false
                  else
                    true
          else
            if a.val < 85 then
              if a.val < 83 then
                true
              else
                if a.val < 84 then
                  true
                else
                  false
            else
              if a.val < 87 then
                false
              else
                if a.val < 88 then
                  false
                else
                  true
        else
          if a.val < 99 then
            if a.val < 94 then
              if a.val < 92 then
                true
              else
                false
            else
              if a.val < 96 then
                false
              else
                true
          else
            if a.val < 103 then
              if a.val < 101 then
                if a.val < 100 then
                  true
                else
                  false
              else
                false
            else
              if a.val < 105 then
                if a.val < 104 then
                  false
                else
                  true
              else
                true
      else
        if a.val < 126 then
          if a.val < 117 then
            if a.val < 112 then
              false
            else
              if a.val < 114 then
                true
              else
                if a.val < 115 then
                  true
                else
                  if a.val < 116 then
                    true
                  else
                    false
          else
            if a.val < 121 then
              if a.val < 119 then
                false
              else
                if a.val < 120 then
                  false
                else
                  true
            else
              if a.val < 123 then
                true
              else
                if a.val < 124 then
                  true
                else
                  false
        else
          if a.val < 135 then
            if a.val < 130 then
              if a.val < 128 then
                false
              else
                true
            else
              if a.val < 132 then
                true
              else
                false
          else
            if a.val < 139 then
              if a.val < 137 then
                if a.val < 136 then
                  false
                else
                  true
              else
                true
            else
              if a.val < 141 then
                if a.val < 140 then
                  true
                else
                  false
              else
                false
  else
    if a.val < 216 then
      if a.val < 180 then
        if a.val < 162 then
          if a.val < 153 then
            if a.val < 148 then
              true
            else
              if a.val < 150 then
                false
              else
                if a.val < 151 then
                  false
                else
                  if a.val < 152 then
                    false
                  else
                    true
          else
            if a.val < 157 then
              if a.val < 155 then
                true
              else
                if a.val < 156 then
                  true
                else
                  false
            else
              if a.val < 159 then
                false
              else
                if a.val < 160 then
                  false
                else
                  true
        else
          if a.val < 171 then
            if a.val < 166 then
              if a.val < 164 then
                true
              else
                false
            else
              if a.val < 168 then
                false
              else
                true
          else
            if a.val < 175 then
              if a.val < 173 then
                if a.val < 172 then
                  true
                else
                  false
              else
                false
            else
              if a.val < 177 then
                if a.val < 176 then
                  false
                else
                  true
              else
                true
      else
        if a.val < 198 then
          if a.val < 189 then
            if a.val < 184 then
              false
            else
              if a.val < 186 then
                true
              else
                if a.val < 187 then
                  true
                else
                  if a.val < 188 then
                    true
                  else
                    false
          else
            if a.val < 193 then
              if a.val < 191 then
                false
              else
                if a.val < 192 then
                  false
                else
                  true
            else
              if a.val < 195 then
                true
              else
                if a.val < 196 then
                  true
                else
                  false
        else
          if a.val < 207 then
            if a.val < 202 then
              if a.val < 200 then
                false
              else
                true
            else
              if a.val < 204 then
                true
              else
                false
          else
            if a.val < 211 then
              if a.val < 209 then
                if a.val < 208 then
                  false
                else
                  true
              else
                true
            else
              if a.val < 213 then
                if a.val < 212 then
                  true
                else
                  false
              else
                false
    else
      if a.val < 252 then
        if a.val < 234 then
          if a.val < 225 then
            if a.val < 220 then
              true
            else
              if a.val < 222 then
                false
              else
                if a.val < 223 then
                  false
                else
                  if a.val < 224 then
                    false
                  else
                    true
          else
            if a.val < 229 then
              if a.val < 227 then
                true
              else
                if a.val < 228 then
                  true
                else
                  false
            else
              if a.val < 231 then
                false
              else
                if a.val < 232 then
                  false
                else
                  true
        else
          if a.val < 243 then
            if a.val < 238 then
              if a.val < 236 then
                true
              else
                false
            else
              false
          else
            if a.val < 247 then
              if a.val < 245 then
                if a.val < 244 then
                  false
                else
                  true
              else
                true
            else
              if a.val < 249 then
                if a.val < 248 then
                  true
                else
                  false
              else
                false
      else
        if a.val < 270 then
          if a.val < 261 then
            if a.val < 256 then
              true
            else
              if a.val < 258 then
                false
              else
                if a.val < 259 then
                  false
                else
                  if a.val < 260 then
                    false
                  else
                    true
          else
            if a.val < 265 then
              if a.val < 263 then
                true
              else
                if a.val < 264 then
                  true
                else
                  false
            else
              if a.val < 267 then
                false
              else
                if a.val < 268 then
                  false
                else
                  true
        else
          if a.val < 279 then
            if a.val < 274 then
              if a.val < 272 then
                true
              else
                false
            else
              if a.val < 276 then
                false
              else
                true
          else
            if a.val < 283 then
              if a.val < 281 then
                if a.val < 280 then
                  true
                else
                  false
              else
                false
            else
              if a.val < 285 then
                if a.val < 284 then
                  false
                else
                  true
              else
                true

def gramSign (a : Fin 288) : GaussianInt := if gramPositive a then 1 else -1
end Math.HiggsFourWaveCubature.Structural.Transverse
