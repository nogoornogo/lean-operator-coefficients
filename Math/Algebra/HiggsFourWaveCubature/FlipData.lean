import Math.Algebra.HiggsFourWaveCubature.Basic

/-! Exact coordinate-sign reindexing data; checked in FlipChecks modules. -/
namespace Math.HiggsFourWaveCubature
set_option autoImplicit false
def flip0_0 (a : Fin 288) : Fin 288 :=
  if a.val < 144 then
    if a.val < 72 then
      if a.val < 36 then
        if a.val < 18 then
          if a.val < 9 then
            if a.val < 4 then
              if a.val < 2 then
                if a.val < 1 then
                  43
                else
                  42
              else
                if a.val < 3 then
                  41
                else
                  40
            else
              if a.val < 6 then
                if a.val < 5 then
                  47
                else
                  46
              else
                if a.val < 7 then
                  45
                else
                  if a.val < 8 then
                    44
                  else
                    35
          else
            if a.val < 13 then
              if a.val < 11 then
                if a.val < 10 then
                  34
                else
                  33
              else
                if a.val < 12 then
                  32
                else
                  39
            else
              if a.val < 15 then
                if a.val < 14 then
                  38
                else
                  37
              else
                if a.val < 16 then
                  36
                else
                  if a.val < 17 then
                    27
                  else
                    26
        else
          if a.val < 27 then
            if a.val < 22 then
              if a.val < 20 then
                if a.val < 19 then
                  25
                else
                  24
              else
                if a.val < 21 then
                  31
                else
                  30
            else
              if a.val < 24 then
                if a.val < 23 then
                  29
                else
                  28
              else
                if a.val < 25 then
                  19
                else
                  if a.val < 26 then
                    18
                  else
                    17
          else
            if a.val < 31 then
              if a.val < 29 then
                if a.val < 28 then
                  16
                else
                  23
              else
                if a.val < 30 then
                  22
                else
                  21
            else
              if a.val < 33 then
                if a.val < 32 then
                  20
                else
                  11
              else
                if a.val < 34 then
                  10
                else
                  if a.val < 35 then
                    9
                  else
                    8
      else
        if a.val < 54 then
          if a.val < 45 then
            if a.val < 40 then
              if a.val < 38 then
                if a.val < 37 then
                  15
                else
                  14
              else
                if a.val < 39 then
                  13
                else
                  12
            else
              if a.val < 42 then
                if a.val < 41 then
                  3
                else
                  2
              else
                if a.val < 43 then
                  1
                else
                  if a.val < 44 then
                    0
                  else
                    7
          else
            if a.val < 49 then
              if a.val < 47 then
                if a.val < 46 then
                  6
                else
                  5
              else
                if a.val < 48 then
                  4
                else
                  233
            else
              if a.val < 51 then
                if a.val < 50 then
                  232
                else
                  235
              else
                if a.val < 52 then
                  234
                else
                  if a.val < 53 then
                    237
                  else
                    236
        else
          if a.val < 63 then
            if a.val < 58 then
              if a.val < 56 then
                if a.val < 55 then
                  239
                else
                  238
              else
                if a.val < 57 then
                  225
                else
                  224
            else
              if a.val < 60 then
                if a.val < 59 then
                  227
                else
                  226
              else
                if a.val < 61 then
                  229
                else
                  if a.val < 62 then
                    228
                  else
                    231
          else
            if a.val < 67 then
              if a.val < 65 then
                if a.val < 64 then
                  230
                else
                  217
              else
                if a.val < 66 then
                  216
                else
                  219
            else
              if a.val < 69 then
                if a.val < 68 then
                  218
                else
                  221
              else
                if a.val < 70 then
                  220
                else
                  if a.val < 71 then
                    223
                  else
                    222
    else
      if a.val < 108 then
        if a.val < 90 then
          if a.val < 81 then
            if a.val < 76 then
              if a.val < 74 then
                if a.val < 73 then
                  209
                else
                  208
              else
                if a.val < 75 then
                  211
                else
                  210
            else
              if a.val < 78 then
                if a.val < 77 then
                  213
                else
                  212
              else
                if a.val < 79 then
                  215
                else
                  if a.val < 80 then
                    214
                  else
                    201
          else
            if a.val < 85 then
              if a.val < 83 then
                if a.val < 82 then
                  200
                else
                  203
              else
                if a.val < 84 then
                  202
                else
                  205
            else
              if a.val < 87 then
                if a.val < 86 then
                  204
                else
                  207
              else
                if a.val < 88 then
                  206
                else
                  if a.val < 89 then
                    193
                  else
                    192
        else
          if a.val < 99 then
            if a.val < 94 then
              if a.val < 92 then
                if a.val < 91 then
                  195
                else
                  194
              else
                if a.val < 93 then
                  197
                else
                  196
            else
              if a.val < 96 then
                if a.val < 95 then
                  199
                else
                  198
              else
                if a.val < 97 then
                  185
                else
                  if a.val < 98 then
                    184
                  else
                    187
          else
            if a.val < 103 then
              if a.val < 101 then
                if a.val < 100 then
                  186
                else
                  189
              else
                if a.val < 102 then
                  188
                else
                  191
            else
              if a.val < 105 then
                if a.val < 104 then
                  190
                else
                  177
              else
                if a.val < 106 then
                  176
                else
                  if a.val < 107 then
                    179
                  else
                    178
      else
        if a.val < 126 then
          if a.val < 117 then
            if a.val < 112 then
              if a.val < 110 then
                if a.val < 109 then
                  181
                else
                  180
              else
                if a.val < 111 then
                  183
                else
                  182
            else
              if a.val < 114 then
                if a.val < 113 then
                  169
                else
                  168
              else
                if a.val < 115 then
                  171
                else
                  if a.val < 116 then
                    170
                  else
                    173
          else
            if a.val < 121 then
              if a.val < 119 then
                if a.val < 118 then
                  172
                else
                  175
              else
                if a.val < 120 then
                  174
                else
                  161
            else
              if a.val < 123 then
                if a.val < 122 then
                  160
                else
                  163
              else
                if a.val < 124 then
                  162
                else
                  if a.val < 125 then
                    165
                  else
                    164
        else
          if a.val < 135 then
            if a.val < 130 then
              if a.val < 128 then
                if a.val < 127 then
                  167
                else
                  166
              else
                if a.val < 129 then
                  153
                else
                  152
            else
              if a.val < 132 then
                if a.val < 131 then
                  155
                else
                  154
              else
                if a.val < 133 then
                  157
                else
                  if a.val < 134 then
                    156
                  else
                    159
          else
            if a.val < 139 then
              if a.val < 137 then
                if a.val < 136 then
                  158
                else
                  145
              else
                if a.val < 138 then
                  144
                else
                  147
            else
              if a.val < 141 then
                if a.val < 140 then
                  146
                else
                  149
              else
                if a.val < 142 then
                  148
                else
                  if a.val < 143 then
                    151
                  else
                    150
  else
    if a.val < 216 then
      if a.val < 180 then
        if a.val < 162 then
          if a.val < 153 then
            if a.val < 148 then
              if a.val < 146 then
                if a.val < 145 then
                  137
                else
                  136
              else
                if a.val < 147 then
                  139
                else
                  138
            else
              if a.val < 150 then
                if a.val < 149 then
                  141
                else
                  140
              else
                if a.val < 151 then
                  143
                else
                  if a.val < 152 then
                    142
                  else
                    129
          else
            if a.val < 157 then
              if a.val < 155 then
                if a.val < 154 then
                  128
                else
                  131
              else
                if a.val < 156 then
                  130
                else
                  133
            else
              if a.val < 159 then
                if a.val < 158 then
                  132
                else
                  135
              else
                if a.val < 160 then
                  134
                else
                  if a.val < 161 then
                    121
                  else
                    120
        else
          if a.val < 171 then
            if a.val < 166 then
              if a.val < 164 then
                if a.val < 163 then
                  123
                else
                  122
              else
                if a.val < 165 then
                  125
                else
                  124
            else
              if a.val < 168 then
                if a.val < 167 then
                  127
                else
                  126
              else
                if a.val < 169 then
                  113
                else
                  if a.val < 170 then
                    112
                  else
                    115
          else
            if a.val < 175 then
              if a.val < 173 then
                if a.val < 172 then
                  114
                else
                  117
              else
                if a.val < 174 then
                  116
                else
                  119
            else
              if a.val < 177 then
                if a.val < 176 then
                  118
                else
                  105
              else
                if a.val < 178 then
                  104
                else
                  if a.val < 179 then
                    107
                  else
                    106
      else
        if a.val < 198 then
          if a.val < 189 then
            if a.val < 184 then
              if a.val < 182 then
                if a.val < 181 then
                  109
                else
                  108
              else
                if a.val < 183 then
                  111
                else
                  110
            else
              if a.val < 186 then
                if a.val < 185 then
                  97
                else
                  96
              else
                if a.val < 187 then
                  99
                else
                  if a.val < 188 then
                    98
                  else
                    101
          else
            if a.val < 193 then
              if a.val < 191 then
                if a.val < 190 then
                  100
                else
                  103
              else
                if a.val < 192 then
                  102
                else
                  89
            else
              if a.val < 195 then
                if a.val < 194 then
                  88
                else
                  91
              else
                if a.val < 196 then
                  90
                else
                  if a.val < 197 then
                    93
                  else
                    92
        else
          if a.val < 207 then
            if a.val < 202 then
              if a.val < 200 then
                if a.val < 199 then
                  95
                else
                  94
              else
                if a.val < 201 then
                  81
                else
                  80
            else
              if a.val < 204 then
                if a.val < 203 then
                  83
                else
                  82
              else
                if a.val < 205 then
                  85
                else
                  if a.val < 206 then
                    84
                  else
                    87
          else
            if a.val < 211 then
              if a.val < 209 then
                if a.val < 208 then
                  86
                else
                  73
              else
                if a.val < 210 then
                  72
                else
                  75
            else
              if a.val < 213 then
                if a.val < 212 then
                  74
                else
                  77
              else
                if a.val < 214 then
                  76
                else
                  if a.val < 215 then
                    79
                  else
                    78
    else
      if a.val < 252 then
        if a.val < 234 then
          if a.val < 225 then
            if a.val < 220 then
              if a.val < 218 then
                if a.val < 217 then
                  65
                else
                  64
              else
                if a.val < 219 then
                  67
                else
                  66
            else
              if a.val < 222 then
                if a.val < 221 then
                  69
                else
                  68
              else
                if a.val < 223 then
                  71
                else
                  if a.val < 224 then
                    70
                  else
                    57
          else
            if a.val < 229 then
              if a.val < 227 then
                if a.val < 226 then
                  56
                else
                  59
              else
                if a.val < 228 then
                  58
                else
                  61
            else
              if a.val < 231 then
                if a.val < 230 then
                  60
                else
                  63
              else
                if a.val < 232 then
                  62
                else
                  if a.val < 233 then
                    49
                  else
                    48
        else
          if a.val < 243 then
            if a.val < 238 then
              if a.val < 236 then
                if a.val < 235 then
                  51
                else
                  50
              else
                if a.val < 237 then
                  53
                else
                  52
            else
              if a.val < 240 then
                if a.val < 239 then
                  55
                else
                  54
              else
                if a.val < 241 then
                  243
                else
                  if a.val < 242 then
                    241
                  else
                    242
          else
            if a.val < 247 then
              if a.val < 245 then
                if a.val < 244 then
                  240
                else
                  247
              else
                if a.val < 246 then
                  245
                else
                  246
            else
              if a.val < 249 then
                if a.val < 248 then
                  244
                else
                  251
              else
                if a.val < 250 then
                  249
                else
                  if a.val < 251 then
                    250
                  else
                    248
      else
        if a.val < 270 then
          if a.val < 261 then
            if a.val < 256 then
              if a.val < 254 then
                if a.val < 253 then
                  255
                else
                  253
              else
                if a.val < 255 then
                  254
                else
                  252
            else
              if a.val < 258 then
                if a.val < 257 then
                  259
                else
                  257
              else
                if a.val < 259 then
                  258
                else
                  if a.val < 260 then
                    256
                  else
                    263
          else
            if a.val < 265 then
              if a.val < 263 then
                if a.val < 262 then
                  261
                else
                  262
              else
                if a.val < 264 then
                  260
                else
                  267
            else
              if a.val < 267 then
                if a.val < 266 then
                  265
                else
                  266
              else
                if a.val < 268 then
                  264
                else
                  if a.val < 269 then
                    271
                  else
                    269
        else
          if a.val < 279 then
            if a.val < 274 then
              if a.val < 272 then
                if a.val < 271 then
                  270
                else
                  268
              else
                if a.val < 273 then
                  275
                else
                  273
            else
              if a.val < 276 then
                if a.val < 275 then
                  274
                else
                  272
              else
                if a.val < 277 then
                  279
                else
                  if a.val < 278 then
                    277
                  else
                    278
          else
            if a.val < 283 then
              if a.val < 281 then
                if a.val < 280 then
                  276
                else
                  283
              else
                if a.val < 282 then
                  281
                else
                  282
            else
              if a.val < 285 then
                if a.val < 284 then
                  280
                else
                  287
              else
                if a.val < 286 then
                  285
                else
                  if a.val < 287 then
                    286
                  else
                    284
def phase0_0 (a : Fin 288) : Fin 4 :=
  if a.val < 144 then
    if a.val < 72 then
      if a.val < 36 then
        if a.val < 18 then
          if a.val < 9 then
            if a.val < 4 then
              if a.val < 2 then
                if a.val < 1 then
                  2
                else
                  2
              else
                if a.val < 3 then
                  2
                else
                  2
            else
              if a.val < 6 then
                if a.val < 5 then
                  2
                else
                  2
              else
                if a.val < 7 then
                  2
                else
                  if a.val < 8 then
                    2
                  else
                    2
          else
            if a.val < 13 then
              if a.val < 11 then
                if a.val < 10 then
                  2
                else
                  2
              else
                if a.val < 12 then
                  2
                else
                  2
            else
              if a.val < 15 then
                if a.val < 14 then
                  2
                else
                  2
              else
                if a.val < 16 then
                  2
                else
                  if a.val < 17 then
                    2
                  else
                    2
        else
          if a.val < 27 then
            if a.val < 22 then
              if a.val < 20 then
                if a.val < 19 then
                  2
                else
                  2
              else
                if a.val < 21 then
                  2
                else
                  2
            else
              if a.val < 24 then
                if a.val < 23 then
                  2
                else
                  2
              else
                if a.val < 25 then
                  2
                else
                  if a.val < 26 then
                    2
                  else
                    2
          else
            if a.val < 31 then
              if a.val < 29 then
                if a.val < 28 then
                  2
                else
                  2
              else
                if a.val < 30 then
                  2
                else
                  2
            else
              if a.val < 33 then
                if a.val < 32 then
                  2
                else
                  2
              else
                if a.val < 34 then
                  2
                else
                  if a.val < 35 then
                    2
                  else
                    2
      else
        if a.val < 54 then
          if a.val < 45 then
            if a.val < 40 then
              if a.val < 38 then
                if a.val < 37 then
                  2
                else
                  2
              else
                if a.val < 39 then
                  2
                else
                  2
            else
              if a.val < 42 then
                if a.val < 41 then
                  2
                else
                  2
              else
                if a.val < 43 then
                  2
                else
                  if a.val < 44 then
                    2
                  else
                    2
          else
            if a.val < 49 then
              if a.val < 47 then
                if a.val < 46 then
                  2
                else
                  2
              else
                if a.val < 48 then
                  2
                else
                  2
            else
              if a.val < 51 then
                if a.val < 50 then
                  2
                else
                  2
              else
                if a.val < 52 then
                  2
                else
                  if a.val < 53 then
                    2
                  else
                    2
        else
          if a.val < 63 then
            if a.val < 58 then
              if a.val < 56 then
                if a.val < 55 then
                  2
                else
                  2
              else
                if a.val < 57 then
                  2
                else
                  2
            else
              if a.val < 60 then
                if a.val < 59 then
                  2
                else
                  2
              else
                if a.val < 61 then
                  2
                else
                  if a.val < 62 then
                    2
                  else
                    2
          else
            if a.val < 67 then
              if a.val < 65 then
                if a.val < 64 then
                  2
                else
                  2
              else
                if a.val < 66 then
                  2
                else
                  2
            else
              if a.val < 69 then
                if a.val < 68 then
                  2
                else
                  2
              else
                if a.val < 70 then
                  2
                else
                  if a.val < 71 then
                    2
                  else
                    2
    else
      if a.val < 108 then
        if a.val < 90 then
          if a.val < 81 then
            if a.val < 76 then
              if a.val < 74 then
                if a.val < 73 then
                  2
                else
                  2
              else
                if a.val < 75 then
                  2
                else
                  2
            else
              if a.val < 78 then
                if a.val < 77 then
                  2
                else
                  2
              else
                if a.val < 79 then
                  2
                else
                  if a.val < 80 then
                    2
                  else
                    2
          else
            if a.val < 85 then
              if a.val < 83 then
                if a.val < 82 then
                  2
                else
                  2
              else
                if a.val < 84 then
                  2
                else
                  2
            else
              if a.val < 87 then
                if a.val < 86 then
                  2
                else
                  2
              else
                if a.val < 88 then
                  2
                else
                  if a.val < 89 then
                    2
                  else
                    2
        else
          if a.val < 99 then
            if a.val < 94 then
              if a.val < 92 then
                if a.val < 91 then
                  2
                else
                  2
              else
                if a.val < 93 then
                  2
                else
                  2
            else
              if a.val < 96 then
                if a.val < 95 then
                  2
                else
                  2
              else
                if a.val < 97 then
                  2
                else
                  if a.val < 98 then
                    2
                  else
                    2
          else
            if a.val < 103 then
              if a.val < 101 then
                if a.val < 100 then
                  2
                else
                  2
              else
                if a.val < 102 then
                  2
                else
                  2
            else
              if a.val < 105 then
                if a.val < 104 then
                  2
                else
                  2
              else
                if a.val < 106 then
                  2
                else
                  if a.val < 107 then
                    2
                  else
                    2
      else
        if a.val < 126 then
          if a.val < 117 then
            if a.val < 112 then
              if a.val < 110 then
                if a.val < 109 then
                  2
                else
                  2
              else
                if a.val < 111 then
                  2
                else
                  2
            else
              if a.val < 114 then
                if a.val < 113 then
                  2
                else
                  2
              else
                if a.val < 115 then
                  2
                else
                  if a.val < 116 then
                    2
                  else
                    2
          else
            if a.val < 121 then
              if a.val < 119 then
                if a.val < 118 then
                  2
                else
                  2
              else
                if a.val < 120 then
                  2
                else
                  2
            else
              if a.val < 123 then
                if a.val < 122 then
                  2
                else
                  2
              else
                if a.val < 124 then
                  2
                else
                  if a.val < 125 then
                    2
                  else
                    2
        else
          if a.val < 135 then
            if a.val < 130 then
              if a.val < 128 then
                if a.val < 127 then
                  2
                else
                  2
              else
                if a.val < 129 then
                  2
                else
                  2
            else
              if a.val < 132 then
                if a.val < 131 then
                  2
                else
                  2
              else
                if a.val < 133 then
                  2
                else
                  if a.val < 134 then
                    2
                  else
                    2
          else
            if a.val < 139 then
              if a.val < 137 then
                if a.val < 136 then
                  2
                else
                  2
              else
                if a.val < 138 then
                  2
                else
                  2
            else
              if a.val < 141 then
                if a.val < 140 then
                  2
                else
                  2
              else
                if a.val < 142 then
                  2
                else
                  if a.val < 143 then
                    2
                  else
                    2
  else
    if a.val < 216 then
      if a.val < 180 then
        if a.val < 162 then
          if a.val < 153 then
            if a.val < 148 then
              if a.val < 146 then
                if a.val < 145 then
                  2
                else
                  2
              else
                if a.val < 147 then
                  2
                else
                  2
            else
              if a.val < 150 then
                if a.val < 149 then
                  2
                else
                  2
              else
                if a.val < 151 then
                  2
                else
                  if a.val < 152 then
                    2
                  else
                    2
          else
            if a.val < 157 then
              if a.val < 155 then
                if a.val < 154 then
                  2
                else
                  2
              else
                if a.val < 156 then
                  2
                else
                  2
            else
              if a.val < 159 then
                if a.val < 158 then
                  2
                else
                  2
              else
                if a.val < 160 then
                  2
                else
                  if a.val < 161 then
                    2
                  else
                    2
        else
          if a.val < 171 then
            if a.val < 166 then
              if a.val < 164 then
                if a.val < 163 then
                  2
                else
                  2
              else
                if a.val < 165 then
                  2
                else
                  2
            else
              if a.val < 168 then
                if a.val < 167 then
                  2
                else
                  2
              else
                if a.val < 169 then
                  2
                else
                  if a.val < 170 then
                    2
                  else
                    2
          else
            if a.val < 175 then
              if a.val < 173 then
                if a.val < 172 then
                  2
                else
                  2
              else
                if a.val < 174 then
                  2
                else
                  2
            else
              if a.val < 177 then
                if a.val < 176 then
                  2
                else
                  2
              else
                if a.val < 178 then
                  2
                else
                  if a.val < 179 then
                    2
                  else
                    2
      else
        if a.val < 198 then
          if a.val < 189 then
            if a.val < 184 then
              if a.val < 182 then
                if a.val < 181 then
                  2
                else
                  2
              else
                if a.val < 183 then
                  2
                else
                  2
            else
              if a.val < 186 then
                if a.val < 185 then
                  2
                else
                  2
              else
                if a.val < 187 then
                  2
                else
                  if a.val < 188 then
                    2
                  else
                    2
          else
            if a.val < 193 then
              if a.val < 191 then
                if a.val < 190 then
                  2
                else
                  2
              else
                if a.val < 192 then
                  2
                else
                  2
            else
              if a.val < 195 then
                if a.val < 194 then
                  2
                else
                  2
              else
                if a.val < 196 then
                  2
                else
                  if a.val < 197 then
                    2
                  else
                    2
        else
          if a.val < 207 then
            if a.val < 202 then
              if a.val < 200 then
                if a.val < 199 then
                  2
                else
                  2
              else
                if a.val < 201 then
                  2
                else
                  2
            else
              if a.val < 204 then
                if a.val < 203 then
                  2
                else
                  2
              else
                if a.val < 205 then
                  2
                else
                  if a.val < 206 then
                    2
                  else
                    2
          else
            if a.val < 211 then
              if a.val < 209 then
                if a.val < 208 then
                  2
                else
                  2
              else
                if a.val < 210 then
                  2
                else
                  2
            else
              if a.val < 213 then
                if a.val < 212 then
                  2
                else
                  2
              else
                if a.val < 214 then
                  2
                else
                  if a.val < 215 then
                    2
                  else
                    2
    else
      if a.val < 252 then
        if a.val < 234 then
          if a.val < 225 then
            if a.val < 220 then
              if a.val < 218 then
                if a.val < 217 then
                  2
                else
                  2
              else
                if a.val < 219 then
                  2
                else
                  2
            else
              if a.val < 222 then
                if a.val < 221 then
                  2
                else
                  2
              else
                if a.val < 223 then
                  2
                else
                  if a.val < 224 then
                    2
                  else
                    2
          else
            if a.val < 229 then
              if a.val < 227 then
                if a.val < 226 then
                  2
                else
                  2
              else
                if a.val < 228 then
                  2
                else
                  2
            else
              if a.val < 231 then
                if a.val < 230 then
                  2
                else
                  2
              else
                if a.val < 232 then
                  2
                else
                  if a.val < 233 then
                    2
                  else
                    2
        else
          if a.val < 243 then
            if a.val < 238 then
              if a.val < 236 then
                if a.val < 235 then
                  2
                else
                  2
              else
                if a.val < 237 then
                  2
                else
                  2
            else
              if a.val < 240 then
                if a.val < 239 then
                  2
                else
                  2
              else
                if a.val < 241 then
                  0
                else
                  if a.val < 242 then
                    0
                  else
                    0
          else
            if a.val < 247 then
              if a.val < 245 then
                if a.val < 244 then
                  0
                else
                  0
              else
                if a.val < 246 then
                  0
                else
                  0
            else
              if a.val < 249 then
                if a.val < 248 then
                  0
                else
                  0
              else
                if a.val < 250 then
                  0
                else
                  if a.val < 251 then
                    0
                  else
                    0
      else
        if a.val < 270 then
          if a.val < 261 then
            if a.val < 256 then
              if a.val < 254 then
                if a.val < 253 then
                  0
                else
                  0
              else
                if a.val < 255 then
                  0
                else
                  0
            else
              if a.val < 258 then
                if a.val < 257 then
                  0
                else
                  0
              else
                if a.val < 259 then
                  0
                else
                  if a.val < 260 then
                    0
                  else
                    0
          else
            if a.val < 265 then
              if a.val < 263 then
                if a.val < 262 then
                  0
                else
                  0
              else
                if a.val < 264 then
                  0
                else
                  0
            else
              if a.val < 267 then
                if a.val < 266 then
                  0
                else
                  0
              else
                if a.val < 268 then
                  0
                else
                  if a.val < 269 then
                    0
                  else
                    0
        else
          if a.val < 279 then
            if a.val < 274 then
              if a.val < 272 then
                if a.val < 271 then
                  0
                else
                  0
              else
                if a.val < 273 then
                  0
                else
                  0
            else
              if a.val < 276 then
                if a.val < 275 then
                  0
                else
                  0
              else
                if a.val < 277 then
                  0
                else
                  if a.val < 278 then
                    0
                  else
                    0
          else
            if a.val < 283 then
              if a.val < 281 then
                if a.val < 280 then
                  0
                else
                  0
              else
                if a.val < 282 then
                  0
                else
                  0
            else
              if a.val < 285 then
                if a.val < 284 then
                  0
                else
                  0
              else
                if a.val < 286 then
                  0
                else
                  if a.val < 287 then
                    0
                  else
                    0
def flip0_1 (a : Fin 288) : Fin 288 :=
  if a.val < 144 then
    if a.val < 72 then
      if a.val < 36 then
        if a.val < 18 then
          if a.val < 9 then
            if a.val < 4 then
              if a.val < 2 then
                if a.val < 1 then
                  40
                else
                  41
              else
                if a.val < 3 then
                  42
                else
                  43
            else
              if a.val < 6 then
                if a.val < 5 then
                  44
                else
                  45
              else
                if a.val < 7 then
                  46
                else
                  if a.val < 8 then
                    47
                  else
                    11
          else
            if a.val < 13 then
              if a.val < 11 then
                if a.val < 10 then
                  9
                else
                  10
              else
                if a.val < 12 then
                  8
                else
                  15
            else
              if a.val < 15 then
                if a.val < 14 then
                  13
                else
                  14
              else
                if a.val < 16 then
                  12
                else
                  if a.val < 17 then
                    19
                  else
                    17
        else
          if a.val < 27 then
            if a.val < 22 then
              if a.val < 20 then
                if a.val < 19 then
                  18
                else
                  16
              else
                if a.val < 21 then
                  23
                else
                  21
            else
              if a.val < 24 then
                if a.val < 23 then
                  22
                else
                  20
              else
                if a.val < 25 then
                  27
                else
                  if a.val < 26 then
                    25
                  else
                    26
          else
            if a.val < 31 then
              if a.val < 29 then
                if a.val < 28 then
                  24
                else
                  31
              else
                if a.val < 30 then
                  29
                else
                  30
            else
              if a.val < 33 then
                if a.val < 32 then
                  28
                else
                  35
              else
                if a.val < 34 then
                  33
                else
                  if a.val < 35 then
                    34
                  else
                    32
      else
        if a.val < 54 then
          if a.val < 45 then
            if a.val < 40 then
              if a.val < 38 then
                if a.val < 37 then
                  39
                else
                  37
              else
                if a.val < 39 then
                  38
                else
                  36
            else
              if a.val < 42 then
                if a.val < 41 then
                  0
                else
                  1
              else
                if a.val < 43 then
                  2
                else
                  if a.val < 44 then
                    3
                  else
                    4
          else
            if a.val < 49 then
              if a.val < 47 then
                if a.val < 46 then
                  5
                else
                  6
              else
                if a.val < 48 then
                  7
                else
                  177
            else
              if a.val < 51 then
                if a.val < 50 then
                  176
                else
                  179
              else
                if a.val < 52 then
                  178
                else
                  if a.val < 53 then
                    181
                  else
                    180
        else
          if a.val < 63 then
            if a.val < 58 then
              if a.val < 56 then
                if a.val < 55 then
                  183
                else
                  182
              else
                if a.val < 57 then
                  185
                else
                  184
            else
              if a.val < 60 then
                if a.val < 59 then
                  187
                else
                  186
              else
                if a.val < 61 then
                  189
                else
                  if a.val < 62 then
                    188
                  else
                    191
          else
            if a.val < 67 then
              if a.val < 65 then
                if a.val < 64 then
                  190
                else
                  193
              else
                if a.val < 66 then
                  192
                else
                  195
            else
              if a.val < 69 then
                if a.val < 68 then
                  194
                else
                  197
              else
                if a.val < 70 then
                  196
                else
                  if a.val < 71 then
                    199
                  else
                    198
    else
      if a.val < 108 then
        if a.val < 90 then
          if a.val < 81 then
            if a.val < 76 then
              if a.val < 74 then
                if a.val < 73 then
                  201
                else
                  200
              else
                if a.val < 75 then
                  203
                else
                  202
            else
              if a.val < 78 then
                if a.val < 77 then
                  205
                else
                  204
              else
                if a.val < 79 then
                  207
                else
                  if a.val < 80 then
                    206
                  else
                    209
          else
            if a.val < 85 then
              if a.val < 83 then
                if a.val < 82 then
                  208
                else
                  211
              else
                if a.val < 84 then
                  210
                else
                  213
            else
              if a.val < 87 then
                if a.val < 86 then
                  212
                else
                  215
              else
                if a.val < 88 then
                  214
                else
                  if a.val < 89 then
                    217
                  else
                    216
        else
          if a.val < 99 then
            if a.val < 94 then
              if a.val < 92 then
                if a.val < 91 then
                  219
                else
                  218
              else
                if a.val < 93 then
                  221
                else
                  220
            else
              if a.val < 96 then
                if a.val < 95 then
                  223
                else
                  222
              else
                if a.val < 97 then
                  225
                else
                  if a.val < 98 then
                    224
                  else
                    227
          else
            if a.val < 103 then
              if a.val < 101 then
                if a.val < 100 then
                  226
                else
                  229
              else
                if a.val < 102 then
                  228
                else
                  231
            else
              if a.val < 105 then
                if a.val < 104 then
                  230
                else
                  233
              else
                if a.val < 106 then
                  232
                else
                  if a.val < 107 then
                    235
                  else
                    234
      else
        if a.val < 126 then
          if a.val < 117 then
            if a.val < 112 then
              if a.val < 110 then
                if a.val < 109 then
                  237
                else
                  236
              else
                if a.val < 111 then
                  239
                else
                  238
            else
              if a.val < 114 then
                if a.val < 113 then
                  144
                else
                  145
              else
                if a.val < 115 then
                  146
                else
                  if a.val < 116 then
                    147
                  else
                    148
          else
            if a.val < 121 then
              if a.val < 119 then
                if a.val < 118 then
                  149
                else
                  150
              else
                if a.val < 120 then
                  151
                else
                  152
            else
              if a.val < 123 then
                if a.val < 122 then
                  153
                else
                  154
              else
                if a.val < 124 then
                  155
                else
                  if a.val < 125 then
                    156
                  else
                    157
        else
          if a.val < 135 then
            if a.val < 130 then
              if a.val < 128 then
                if a.val < 127 then
                  158
                else
                  159
              else
                if a.val < 129 then
                  160
                else
                  161
            else
              if a.val < 132 then
                if a.val < 131 then
                  162
                else
                  163
              else
                if a.val < 133 then
                  164
                else
                  if a.val < 134 then
                    165
                  else
                    166
          else
            if a.val < 139 then
              if a.val < 137 then
                if a.val < 136 then
                  167
                else
                  168
              else
                if a.val < 138 then
                  169
                else
                  170
            else
              if a.val < 141 then
                if a.val < 140 then
                  171
                else
                  172
              else
                if a.val < 142 then
                  173
                else
                  if a.val < 143 then
                    174
                  else
                    175
  else
    if a.val < 216 then
      if a.val < 180 then
        if a.val < 162 then
          if a.val < 153 then
            if a.val < 148 then
              if a.val < 146 then
                if a.val < 145 then
                  112
                else
                  113
              else
                if a.val < 147 then
                  114
                else
                  115
            else
              if a.val < 150 then
                if a.val < 149 then
                  116
                else
                  117
              else
                if a.val < 151 then
                  118
                else
                  if a.val < 152 then
                    119
                  else
                    120
          else
            if a.val < 157 then
              if a.val < 155 then
                if a.val < 154 then
                  121
                else
                  122
              else
                if a.val < 156 then
                  123
                else
                  124
            else
              if a.val < 159 then
                if a.val < 158 then
                  125
                else
                  126
              else
                if a.val < 160 then
                  127
                else
                  if a.val < 161 then
                    128
                  else
                    129
        else
          if a.val < 171 then
            if a.val < 166 then
              if a.val < 164 then
                if a.val < 163 then
                  130
                else
                  131
              else
                if a.val < 165 then
                  132
                else
                  133
            else
              if a.val < 168 then
                if a.val < 167 then
                  134
                else
                  135
              else
                if a.val < 169 then
                  136
                else
                  if a.val < 170 then
                    137
                  else
                    138
          else
            if a.val < 175 then
              if a.val < 173 then
                if a.val < 172 then
                  139
                else
                  140
              else
                if a.val < 174 then
                  141
                else
                  142
            else
              if a.val < 177 then
                if a.val < 176 then
                  143
                else
                  49
              else
                if a.val < 178 then
                  48
                else
                  if a.val < 179 then
                    51
                  else
                    50
      else
        if a.val < 198 then
          if a.val < 189 then
            if a.val < 184 then
              if a.val < 182 then
                if a.val < 181 then
                  53
                else
                  52
              else
                if a.val < 183 then
                  55
                else
                  54
            else
              if a.val < 186 then
                if a.val < 185 then
                  57
                else
                  56
              else
                if a.val < 187 then
                  59
                else
                  if a.val < 188 then
                    58
                  else
                    61
          else
            if a.val < 193 then
              if a.val < 191 then
                if a.val < 190 then
                  60
                else
                  63
              else
                if a.val < 192 then
                  62
                else
                  65
            else
              if a.val < 195 then
                if a.val < 194 then
                  64
                else
                  67
              else
                if a.val < 196 then
                  66
                else
                  if a.val < 197 then
                    69
                  else
                    68
        else
          if a.val < 207 then
            if a.val < 202 then
              if a.val < 200 then
                if a.val < 199 then
                  71
                else
                  70
              else
                if a.val < 201 then
                  73
                else
                  72
            else
              if a.val < 204 then
                if a.val < 203 then
                  75
                else
                  74
              else
                if a.val < 205 then
                  77
                else
                  if a.val < 206 then
                    76
                  else
                    79
          else
            if a.val < 211 then
              if a.val < 209 then
                if a.val < 208 then
                  78
                else
                  81
              else
                if a.val < 210 then
                  80
                else
                  83
            else
              if a.val < 213 then
                if a.val < 212 then
                  82
                else
                  85
              else
                if a.val < 214 then
                  84
                else
                  if a.val < 215 then
                    87
                  else
                    86
    else
      if a.val < 252 then
        if a.val < 234 then
          if a.val < 225 then
            if a.val < 220 then
              if a.val < 218 then
                if a.val < 217 then
                  89
                else
                  88
              else
                if a.val < 219 then
                  91
                else
                  90
            else
              if a.val < 222 then
                if a.val < 221 then
                  93
                else
                  92
              else
                if a.val < 223 then
                  95
                else
                  if a.val < 224 then
                    94
                  else
                    97
          else
            if a.val < 229 then
              if a.val < 227 then
                if a.val < 226 then
                  96
                else
                  99
              else
                if a.val < 228 then
                  98
                else
                  101
            else
              if a.val < 231 then
                if a.val < 230 then
                  100
                else
                  103
              else
                if a.val < 232 then
                  102
                else
                  if a.val < 233 then
                    105
                  else
                    104
        else
          if a.val < 243 then
            if a.val < 238 then
              if a.val < 236 then
                if a.val < 235 then
                  107
                else
                  106
              else
                if a.val < 237 then
                  109
                else
                  108
            else
              if a.val < 240 then
                if a.val < 239 then
                  111
                else
                  110
              else
                if a.val < 241 then
                  267
                else
                  if a.val < 242 then
                    266
                  else
                    265
          else
            if a.val < 247 then
              if a.val < 245 then
                if a.val < 244 then
                  264
                else
                  271
              else
                if a.val < 246 then
                  270
                else
                  269
            else
              if a.val < 249 then
                if a.val < 248 then
                  268
                else
                  259
              else
                if a.val < 250 then
                  258
                else
                  if a.val < 251 then
                    257
                  else
                    256
      else
        if a.val < 270 then
          if a.val < 261 then
            if a.val < 256 then
              if a.val < 254 then
                if a.val < 253 then
                  263
                else
                  262
              else
                if a.val < 255 then
                  261
                else
                  260
            else
              if a.val < 258 then
                if a.val < 257 then
                  251
                else
                  250
              else
                if a.val < 259 then
                  249
                else
                  if a.val < 260 then
                    248
                  else
                    255
          else
            if a.val < 265 then
              if a.val < 263 then
                if a.val < 262 then
                  254
                else
                  253
              else
                if a.val < 264 then
                  252
                else
                  243
            else
              if a.val < 267 then
                if a.val < 266 then
                  242
                else
                  241
              else
                if a.val < 268 then
                  240
                else
                  if a.val < 269 then
                    247
                  else
                    246
        else
          if a.val < 279 then
            if a.val < 274 then
              if a.val < 272 then
                if a.val < 271 then
                  245
                else
                  244
              else
                if a.val < 273 then
                  272
                else
                  274
            else
              if a.val < 276 then
                if a.val < 275 then
                  273
                else
                  275
              else
                if a.val < 277 then
                  276
                else
                  if a.val < 278 then
                    278
                  else
                    277
          else
            if a.val < 283 then
              if a.val < 281 then
                if a.val < 280 then
                  279
                else
                  280
              else
                if a.val < 282 then
                  282
                else
                  281
            else
              if a.val < 285 then
                if a.val < 284 then
                  283
                else
                  284
              else
                if a.val < 286 then
                  286
                else
                  if a.val < 287 then
                    285
                  else
                    287
def phase0_1 (a : Fin 288) : Fin 4 :=
  if a.val < 144 then
    if a.val < 72 then
      if a.val < 36 then
        if a.val < 18 then
          if a.val < 9 then
            if a.val < 4 then
              if a.val < 2 then
                if a.val < 1 then
                  0
                else
                  0
              else
                if a.val < 3 then
                  0
                else
                  0
            else
              if a.val < 6 then
                if a.val < 5 then
                  0
                else
                  0
              else
                if a.val < 7 then
                  0
                else
                  if a.val < 8 then
                    0
                  else
                    0
          else
            if a.val < 13 then
              if a.val < 11 then
                if a.val < 10 then
                  0
                else
                  0
              else
                if a.val < 12 then
                  0
                else
                  0
            else
              if a.val < 15 then
                if a.val < 14 then
                  0
                else
                  0
              else
                if a.val < 16 then
                  0
                else
                  if a.val < 17 then
                    0
                  else
                    0
        else
          if a.val < 27 then
            if a.val < 22 then
              if a.val < 20 then
                if a.val < 19 then
                  0
                else
                  0
              else
                if a.val < 21 then
                  0
                else
                  0
            else
              if a.val < 24 then
                if a.val < 23 then
                  0
                else
                  0
              else
                if a.val < 25 then
                  0
                else
                  if a.val < 26 then
                    0
                  else
                    0
          else
            if a.val < 31 then
              if a.val < 29 then
                if a.val < 28 then
                  0
                else
                  0
              else
                if a.val < 30 then
                  0
                else
                  0
            else
              if a.val < 33 then
                if a.val < 32 then
                  0
                else
                  0
              else
                if a.val < 34 then
                  0
                else
                  if a.val < 35 then
                    0
                  else
                    0
      else
        if a.val < 54 then
          if a.val < 45 then
            if a.val < 40 then
              if a.val < 38 then
                if a.val < 37 then
                  0
                else
                  0
              else
                if a.val < 39 then
                  0
                else
                  0
            else
              if a.val < 42 then
                if a.val < 41 then
                  0
                else
                  0
              else
                if a.val < 43 then
                  0
                else
                  if a.val < 44 then
                    0
                  else
                    0
          else
            if a.val < 49 then
              if a.val < 47 then
                if a.val < 46 then
                  0
                else
                  0
              else
                if a.val < 48 then
                  0
                else
                  0
            else
              if a.val < 51 then
                if a.val < 50 then
                  0
                else
                  0
              else
                if a.val < 52 then
                  0
                else
                  if a.val < 53 then
                    0
                  else
                    0
        else
          if a.val < 63 then
            if a.val < 58 then
              if a.val < 56 then
                if a.val < 55 then
                  0
                else
                  0
              else
                if a.val < 57 then
                  0
                else
                  0
            else
              if a.val < 60 then
                if a.val < 59 then
                  0
                else
                  0
              else
                if a.val < 61 then
                  0
                else
                  if a.val < 62 then
                    0
                  else
                    0
          else
            if a.val < 67 then
              if a.val < 65 then
                if a.val < 64 then
                  0
                else
                  0
              else
                if a.val < 66 then
                  0
                else
                  0
            else
              if a.val < 69 then
                if a.val < 68 then
                  0
                else
                  0
              else
                if a.val < 70 then
                  0
                else
                  if a.val < 71 then
                    0
                  else
                    0
    else
      if a.val < 108 then
        if a.val < 90 then
          if a.val < 81 then
            if a.val < 76 then
              if a.val < 74 then
                if a.val < 73 then
                  0
                else
                  0
              else
                if a.val < 75 then
                  0
                else
                  0
            else
              if a.val < 78 then
                if a.val < 77 then
                  0
                else
                  0
              else
                if a.val < 79 then
                  0
                else
                  if a.val < 80 then
                    0
                  else
                    0
          else
            if a.val < 85 then
              if a.val < 83 then
                if a.val < 82 then
                  0
                else
                  0
              else
                if a.val < 84 then
                  0
                else
                  0
            else
              if a.val < 87 then
                if a.val < 86 then
                  0
                else
                  0
              else
                if a.val < 88 then
                  0
                else
                  if a.val < 89 then
                    0
                  else
                    0
        else
          if a.val < 99 then
            if a.val < 94 then
              if a.val < 92 then
                if a.val < 91 then
                  0
                else
                  0
              else
                if a.val < 93 then
                  0
                else
                  0
            else
              if a.val < 96 then
                if a.val < 95 then
                  0
                else
                  0
              else
                if a.val < 97 then
                  0
                else
                  if a.val < 98 then
                    0
                  else
                    0
          else
            if a.val < 103 then
              if a.val < 101 then
                if a.val < 100 then
                  0
                else
                  0
              else
                if a.val < 102 then
                  0
                else
                  0
            else
              if a.val < 105 then
                if a.val < 104 then
                  0
                else
                  0
              else
                if a.val < 106 then
                  0
                else
                  if a.val < 107 then
                    0
                  else
                    0
      else
        if a.val < 126 then
          if a.val < 117 then
            if a.val < 112 then
              if a.val < 110 then
                if a.val < 109 then
                  0
                else
                  0
              else
                if a.val < 111 then
                  0
                else
                  0
            else
              if a.val < 114 then
                if a.val < 113 then
                  0
                else
                  0
              else
                if a.val < 115 then
                  0
                else
                  if a.val < 116 then
                    0
                  else
                    0
          else
            if a.val < 121 then
              if a.val < 119 then
                if a.val < 118 then
                  0
                else
                  0
              else
                if a.val < 120 then
                  0
                else
                  0
            else
              if a.val < 123 then
                if a.val < 122 then
                  0
                else
                  0
              else
                if a.val < 124 then
                  0
                else
                  if a.val < 125 then
                    0
                  else
                    0
        else
          if a.val < 135 then
            if a.val < 130 then
              if a.val < 128 then
                if a.val < 127 then
                  0
                else
                  0
              else
                if a.val < 129 then
                  0
                else
                  0
            else
              if a.val < 132 then
                if a.val < 131 then
                  0
                else
                  0
              else
                if a.val < 133 then
                  0
                else
                  if a.val < 134 then
                    0
                  else
                    0
          else
            if a.val < 139 then
              if a.val < 137 then
                if a.val < 136 then
                  0
                else
                  0
              else
                if a.val < 138 then
                  0
                else
                  0
            else
              if a.val < 141 then
                if a.val < 140 then
                  0
                else
                  0
              else
                if a.val < 142 then
                  0
                else
                  if a.val < 143 then
                    0
                  else
                    0
  else
    if a.val < 216 then
      if a.val < 180 then
        if a.val < 162 then
          if a.val < 153 then
            if a.val < 148 then
              if a.val < 146 then
                if a.val < 145 then
                  0
                else
                  0
              else
                if a.val < 147 then
                  0
                else
                  0
            else
              if a.val < 150 then
                if a.val < 149 then
                  0
                else
                  0
              else
                if a.val < 151 then
                  0
                else
                  if a.val < 152 then
                    0
                  else
                    0
          else
            if a.val < 157 then
              if a.val < 155 then
                if a.val < 154 then
                  0
                else
                  0
              else
                if a.val < 156 then
                  0
                else
                  0
            else
              if a.val < 159 then
                if a.val < 158 then
                  0
                else
                  0
              else
                if a.val < 160 then
                  0
                else
                  if a.val < 161 then
                    0
                  else
                    0
        else
          if a.val < 171 then
            if a.val < 166 then
              if a.val < 164 then
                if a.val < 163 then
                  0
                else
                  0
              else
                if a.val < 165 then
                  0
                else
                  0
            else
              if a.val < 168 then
                if a.val < 167 then
                  0
                else
                  0
              else
                if a.val < 169 then
                  0
                else
                  if a.val < 170 then
                    0
                  else
                    0
          else
            if a.val < 175 then
              if a.val < 173 then
                if a.val < 172 then
                  0
                else
                  0
              else
                if a.val < 174 then
                  0
                else
                  0
            else
              if a.val < 177 then
                if a.val < 176 then
                  0
                else
                  0
              else
                if a.val < 178 then
                  0
                else
                  if a.val < 179 then
                    0
                  else
                    0
      else
        if a.val < 198 then
          if a.val < 189 then
            if a.val < 184 then
              if a.val < 182 then
                if a.val < 181 then
                  0
                else
                  0
              else
                if a.val < 183 then
                  0
                else
                  0
            else
              if a.val < 186 then
                if a.val < 185 then
                  0
                else
                  0
              else
                if a.val < 187 then
                  0
                else
                  if a.val < 188 then
                    0
                  else
                    0
          else
            if a.val < 193 then
              if a.val < 191 then
                if a.val < 190 then
                  0
                else
                  0
              else
                if a.val < 192 then
                  0
                else
                  0
            else
              if a.val < 195 then
                if a.val < 194 then
                  0
                else
                  0
              else
                if a.val < 196 then
                  0
                else
                  if a.val < 197 then
                    0
                  else
                    0
        else
          if a.val < 207 then
            if a.val < 202 then
              if a.val < 200 then
                if a.val < 199 then
                  0
                else
                  0
              else
                if a.val < 201 then
                  0
                else
                  0
            else
              if a.val < 204 then
                if a.val < 203 then
                  0
                else
                  0
              else
                if a.val < 205 then
                  0
                else
                  if a.val < 206 then
                    0
                  else
                    0
          else
            if a.val < 211 then
              if a.val < 209 then
                if a.val < 208 then
                  0
                else
                  0
              else
                if a.val < 210 then
                  0
                else
                  0
            else
              if a.val < 213 then
                if a.val < 212 then
                  0
                else
                  0
              else
                if a.val < 214 then
                  0
                else
                  if a.val < 215 then
                    0
                  else
                    0
    else
      if a.val < 252 then
        if a.val < 234 then
          if a.val < 225 then
            if a.val < 220 then
              if a.val < 218 then
                if a.val < 217 then
                  0
                else
                  0
              else
                if a.val < 219 then
                  0
                else
                  0
            else
              if a.val < 222 then
                if a.val < 221 then
                  0
                else
                  0
              else
                if a.val < 223 then
                  0
                else
                  if a.val < 224 then
                    0
                  else
                    0
          else
            if a.val < 229 then
              if a.val < 227 then
                if a.val < 226 then
                  0
                else
                  0
              else
                if a.val < 228 then
                  0
                else
                  0
            else
              if a.val < 231 then
                if a.val < 230 then
                  0
                else
                  0
              else
                if a.val < 232 then
                  0
                else
                  if a.val < 233 then
                    0
                  else
                    0
        else
          if a.val < 243 then
            if a.val < 238 then
              if a.val < 236 then
                if a.val < 235 then
                  0
                else
                  0
              else
                if a.val < 237 then
                  0
                else
                  0
            else
              if a.val < 240 then
                if a.val < 239 then
                  0
                else
                  0
              else
                if a.val < 241 then
                  2
                else
                  if a.val < 242 then
                    2
                  else
                    2
          else
            if a.val < 247 then
              if a.val < 245 then
                if a.val < 244 then
                  2
                else
                  2
              else
                if a.val < 246 then
                  2
                else
                  2
            else
              if a.val < 249 then
                if a.val < 248 then
                  2
                else
                  2
              else
                if a.val < 250 then
                  2
                else
                  if a.val < 251 then
                    2
                  else
                    2
      else
        if a.val < 270 then
          if a.val < 261 then
            if a.val < 256 then
              if a.val < 254 then
                if a.val < 253 then
                  2
                else
                  2
              else
                if a.val < 255 then
                  2
                else
                  2
            else
              if a.val < 258 then
                if a.val < 257 then
                  2
                else
                  2
              else
                if a.val < 259 then
                  2
                else
                  if a.val < 260 then
                    2
                  else
                    2
          else
            if a.val < 265 then
              if a.val < 263 then
                if a.val < 262 then
                  2
                else
                  2
              else
                if a.val < 264 then
                  2
                else
                  2
            else
              if a.val < 267 then
                if a.val < 266 then
                  2
                else
                  2
              else
                if a.val < 268 then
                  2
                else
                  if a.val < 269 then
                    2
                  else
                    2
        else
          if a.val < 279 then
            if a.val < 274 then
              if a.val < 272 then
                if a.val < 271 then
                  2
                else
                  2
              else
                if a.val < 273 then
                  0
                else
                  0
            else
              if a.val < 276 then
                if a.val < 275 then
                  0
                else
                  0
              else
                if a.val < 277 then
                  0
                else
                  if a.val < 278 then
                    0
                  else
                    0
          else
            if a.val < 283 then
              if a.val < 281 then
                if a.val < 280 then
                  0
                else
                  0
              else
                if a.val < 282 then
                  0
                else
                  0
            else
              if a.val < 285 then
                if a.val < 284 then
                  0
                else
                  0
              else
                if a.val < 286 then
                  0
                else
                  if a.val < 287 then
                    0
                  else
                    0
def flip0_2 (a : Fin 288) : Fin 288 :=
  if a.val < 144 then
    if a.val < 72 then
      if a.val < 36 then
        if a.val < 18 then
          if a.val < 9 then
            if a.val < 4 then
              if a.val < 2 then
                if a.val < 1 then
                  3
                else
                  1
              else
                if a.val < 3 then
                  2
                else
                  0
            else
              if a.val < 6 then
                if a.val < 5 then
                  7
                else
                  5
              else
                if a.val < 7 then
                  6
                else
                  if a.val < 8 then
                    4
                  else
                    32
          else
            if a.val < 13 then
              if a.val < 11 then
                if a.val < 10 then
                  33
                else
                  34
              else
                if a.val < 12 then
                  35
                else
                  36
            else
              if a.val < 15 then
                if a.val < 14 then
                  37
                else
                  38
              else
                if a.val < 16 then
                  39
                else
                  if a.val < 17 then
                    16
                  else
                    18
        else
          if a.val < 27 then
            if a.val < 22 then
              if a.val < 20 then
                if a.val < 19 then
                  17
                else
                  19
              else
                if a.val < 21 then
                  20
                else
                  22
            else
              if a.val < 24 then
                if a.val < 23 then
                  21
                else
                  23
              else
                if a.val < 25 then
                  24
                else
                  if a.val < 26 then
                    26
                  else
                    25
          else
            if a.val < 31 then
              if a.val < 29 then
                if a.val < 28 then
                  27
                else
                  28
              else
                if a.val < 30 then
                  30
                else
                  29
            else
              if a.val < 33 then
                if a.val < 32 then
                  31
                else
                  8
              else
                if a.val < 34 then
                  9
                else
                  if a.val < 35 then
                    10
                  else
                    11
      else
        if a.val < 54 then
          if a.val < 45 then
            if a.val < 40 then
              if a.val < 38 then
                if a.val < 37 then
                  12
                else
                  13
              else
                if a.val < 39 then
                  14
                else
                  15
            else
              if a.val < 42 then
                if a.val < 41 then
                  43
                else
                  41
              else
                if a.val < 43 then
                  42
                else
                  if a.val < 44 then
                    40
                  else
                    47
          else
            if a.val < 49 then
              if a.val < 47 then
                if a.val < 46 then
                  45
                else
                  46
              else
                if a.val < 48 then
                  44
                else
                  96
            else
              if a.val < 51 then
                if a.val < 50 then
                  97
                else
                  98
              else
                if a.val < 52 then
                  99
                else
                  if a.val < 53 then
                    100
                  else
                    101
        else
          if a.val < 63 then
            if a.val < 58 then
              if a.val < 56 then
                if a.val < 55 then
                  102
                else
                  103
              else
                if a.val < 57 then
                  104
                else
                  105
            else
              if a.val < 60 then
                if a.val < 59 then
                  106
                else
                  107
              else
                if a.val < 61 then
                  108
                else
                  if a.val < 62 then
                    109
                  else
                    110
          else
            if a.val < 67 then
              if a.val < 65 then
                if a.val < 64 then
                  111
                else
                  80
              else
                if a.val < 66 then
                  81
                else
                  82
            else
              if a.val < 69 then
                if a.val < 68 then
                  83
                else
                  84
              else
                if a.val < 70 then
                  85
                else
                  if a.val < 71 then
                    86
                  else
                    87
    else
      if a.val < 108 then
        if a.val < 90 then
          if a.val < 81 then
            if a.val < 76 then
              if a.val < 74 then
                if a.val < 73 then
                  88
                else
                  89
              else
                if a.val < 75 then
                  90
                else
                  91
            else
              if a.val < 78 then
                if a.val < 77 then
                  92
                else
                  93
              else
                if a.val < 79 then
                  94
                else
                  if a.val < 80 then
                    95
                  else
                    64
          else
            if a.val < 85 then
              if a.val < 83 then
                if a.val < 82 then
                  65
                else
                  66
              else
                if a.val < 84 then
                  67
                else
                  68
            else
              if a.val < 87 then
                if a.val < 86 then
                  69
                else
                  70
              else
                if a.val < 88 then
                  71
                else
                  if a.val < 89 then
                    72
                  else
                    73
        else
          if a.val < 99 then
            if a.val < 94 then
              if a.val < 92 then
                if a.val < 91 then
                  74
                else
                  75
              else
                if a.val < 93 then
                  76
                else
                  77
            else
              if a.val < 96 then
                if a.val < 95 then
                  78
                else
                  79
              else
                if a.val < 97 then
                  48
                else
                  if a.val < 98 then
                    49
                  else
                    50
          else
            if a.val < 103 then
              if a.val < 101 then
                if a.val < 100 then
                  51
                else
                  52
              else
                if a.val < 102 then
                  53
                else
                  54
            else
              if a.val < 105 then
                if a.val < 104 then
                  55
                else
                  56
              else
                if a.val < 106 then
                  57
                else
                  if a.val < 107 then
                    58
                  else
                    59
      else
        if a.val < 126 then
          if a.val < 117 then
            if a.val < 112 then
              if a.val < 110 then
                if a.val < 109 then
                  60
                else
                  61
              else
                if a.val < 111 then
                  62
                else
                  63
            else
              if a.val < 114 then
                if a.val < 113 then
                  129
                else
                  128
              else
                if a.val < 115 then
                  131
                else
                  if a.val < 116 then
                    130
                  else
                    133
          else
            if a.val < 121 then
              if a.val < 119 then
                if a.val < 118 then
                  132
                else
                  135
              else
                if a.val < 120 then
                  134
                else
                  137
            else
              if a.val < 123 then
                if a.val < 122 then
                  136
                else
                  139
              else
                if a.val < 124 then
                  138
                else
                  if a.val < 125 then
                    141
                  else
                    140
        else
          if a.val < 135 then
            if a.val < 130 then
              if a.val < 128 then
                if a.val < 127 then
                  143
                else
                  142
              else
                if a.val < 129 then
                  113
                else
                  112
            else
              if a.val < 132 then
                if a.val < 131 then
                  115
                else
                  114
              else
                if a.val < 133 then
                  117
                else
                  if a.val < 134 then
                    116
                  else
                    119
          else
            if a.val < 139 then
              if a.val < 137 then
                if a.val < 136 then
                  118
                else
                  121
              else
                if a.val < 138 then
                  120
                else
                  123
            else
              if a.val < 141 then
                if a.val < 140 then
                  122
                else
                  125
              else
                if a.val < 142 then
                  124
                else
                  if a.val < 143 then
                    127
                  else
                    126
  else
    if a.val < 216 then
      if a.val < 180 then
        if a.val < 162 then
          if a.val < 153 then
            if a.val < 148 then
              if a.val < 146 then
                if a.val < 145 then
                  161
                else
                  160
              else
                if a.val < 147 then
                  163
                else
                  162
            else
              if a.val < 150 then
                if a.val < 149 then
                  165
                else
                  164
              else
                if a.val < 151 then
                  167
                else
                  if a.val < 152 then
                    166
                  else
                    169
          else
            if a.val < 157 then
              if a.val < 155 then
                if a.val < 154 then
                  168
                else
                  171
              else
                if a.val < 156 then
                  170
                else
                  173
            else
              if a.val < 159 then
                if a.val < 158 then
                  172
                else
                  175
              else
                if a.val < 160 then
                  174
                else
                  if a.val < 161 then
                    145
                  else
                    144
        else
          if a.val < 171 then
            if a.val < 166 then
              if a.val < 164 then
                if a.val < 163 then
                  147
                else
                  146
              else
                if a.val < 165 then
                  149
                else
                  148
            else
              if a.val < 168 then
                if a.val < 167 then
                  151
                else
                  150
              else
                if a.val < 169 then
                  153
                else
                  if a.val < 170 then
                    152
                  else
                    155
          else
            if a.val < 175 then
              if a.val < 173 then
                if a.val < 172 then
                  154
                else
                  157
              else
                if a.val < 174 then
                  156
                else
                  159
            else
              if a.val < 177 then
                if a.val < 176 then
                  158
                else
                  224
              else
                if a.val < 178 then
                  225
                else
                  if a.val < 179 then
                    226
                  else
                    227
      else
        if a.val < 198 then
          if a.val < 189 then
            if a.val < 184 then
              if a.val < 182 then
                if a.val < 181 then
                  228
                else
                  229
              else
                if a.val < 183 then
                  230
                else
                  231
            else
              if a.val < 186 then
                if a.val < 185 then
                  232
                else
                  233
              else
                if a.val < 187 then
                  234
                else
                  if a.val < 188 then
                    235
                  else
                    236
          else
            if a.val < 193 then
              if a.val < 191 then
                if a.val < 190 then
                  237
                else
                  238
              else
                if a.val < 192 then
                  239
                else
                  208
            else
              if a.val < 195 then
                if a.val < 194 then
                  209
                else
                  210
              else
                if a.val < 196 then
                  211
                else
                  if a.val < 197 then
                    212
                  else
                    213
        else
          if a.val < 207 then
            if a.val < 202 then
              if a.val < 200 then
                if a.val < 199 then
                  214
                else
                  215
              else
                if a.val < 201 then
                  216
                else
                  217
            else
              if a.val < 204 then
                if a.val < 203 then
                  218
                else
                  219
              else
                if a.val < 205 then
                  220
                else
                  if a.val < 206 then
                    221
                  else
                    222
          else
            if a.val < 211 then
              if a.val < 209 then
                if a.val < 208 then
                  223
                else
                  192
              else
                if a.val < 210 then
                  193
                else
                  194
            else
              if a.val < 213 then
                if a.val < 212 then
                  195
                else
                  196
              else
                if a.val < 214 then
                  197
                else
                  if a.val < 215 then
                    198
                  else
                    199
    else
      if a.val < 252 then
        if a.val < 234 then
          if a.val < 225 then
            if a.val < 220 then
              if a.val < 218 then
                if a.val < 217 then
                  200
                else
                  201
              else
                if a.val < 219 then
                  202
                else
                  203
            else
              if a.val < 222 then
                if a.val < 221 then
                  204
                else
                  205
              else
                if a.val < 223 then
                  206
                else
                  if a.val < 224 then
                    207
                  else
                    176
          else
            if a.val < 229 then
              if a.val < 227 then
                if a.val < 226 then
                  177
                else
                  178
              else
                if a.val < 228 then
                  179
                else
                  180
            else
              if a.val < 231 then
                if a.val < 230 then
                  181
                else
                  182
              else
                if a.val < 232 then
                  183
                else
                  if a.val < 233 then
                    184
                  else
                    185
        else
          if a.val < 243 then
            if a.val < 238 then
              if a.val < 236 then
                if a.val < 235 then
                  186
                else
                  187
              else
                if a.val < 237 then
                  188
                else
                  189
            else
              if a.val < 240 then
                if a.val < 239 then
                  190
                else
                  191
              else
                if a.val < 241 then
                  264
                else
                  if a.val < 242 then
                    265
                  else
                    266
          else
            if a.val < 247 then
              if a.val < 245 then
                if a.val < 244 then
                  267
                else
                  268
              else
                if a.val < 246 then
                  269
                else
                  270
            else
              if a.val < 249 then
                if a.val < 248 then
                  271
                else
                  248
              else
                if a.val < 250 then
                  250
                else
                  if a.val < 251 then
                    249
                  else
                    251
      else
        if a.val < 270 then
          if a.val < 261 then
            if a.val < 256 then
              if a.val < 254 then
                if a.val < 253 then
                  252
                else
                  254
              else
                if a.val < 255 then
                  253
                else
                  255
            else
              if a.val < 258 then
                if a.val < 257 then
                  256
                else
                  258
              else
                if a.val < 259 then
                  257
                else
                  if a.val < 260 then
                    259
                  else
                    260
          else
            if a.val < 265 then
              if a.val < 263 then
                if a.val < 262 then
                  262
                else
                  261
              else
                if a.val < 264 then
                  263
                else
                  240
            else
              if a.val < 267 then
                if a.val < 266 then
                  241
                else
                  242
              else
                if a.val < 268 then
                  243
                else
                  if a.val < 269 then
                    244
                  else
                    245
        else
          if a.val < 279 then
            if a.val < 274 then
              if a.val < 272 then
                if a.val < 271 then
                  246
                else
                  247
              else
                if a.val < 273 then
                  283
                else
                  282
            else
              if a.val < 276 then
                if a.val < 275 then
                  281
                else
                  280
              else
                if a.val < 277 then
                  287
                else
                  if a.val < 278 then
                    286
                  else
                    285
          else
            if a.val < 283 then
              if a.val < 281 then
                if a.val < 280 then
                  284
                else
                  275
              else
                if a.val < 282 then
                  274
                else
                  273
            else
              if a.val < 285 then
                if a.val < 284 then
                  272
                else
                  279
              else
                if a.val < 286 then
                  278
                else
                  if a.val < 287 then
                    277
                  else
                    276
def phase0_2 (a : Fin 288) : Fin 4 :=
  if a.val < 144 then
    if a.val < 72 then
      if a.val < 36 then
        if a.val < 18 then
          if a.val < 9 then
            if a.val < 4 then
              if a.val < 2 then
                if a.val < 1 then
                  0
                else
                  0
              else
                if a.val < 3 then
                  0
                else
                  0
            else
              if a.val < 6 then
                if a.val < 5 then
                  0
                else
                  0
              else
                if a.val < 7 then
                  0
                else
                  if a.val < 8 then
                    0
                  else
                    0
          else
            if a.val < 13 then
              if a.val < 11 then
                if a.val < 10 then
                  0
                else
                  0
              else
                if a.val < 12 then
                  0
                else
                  0
            else
              if a.val < 15 then
                if a.val < 14 then
                  0
                else
                  0
              else
                if a.val < 16 then
                  0
                else
                  if a.val < 17 then
                    0
                  else
                    0
        else
          if a.val < 27 then
            if a.val < 22 then
              if a.val < 20 then
                if a.val < 19 then
                  0
                else
                  0
              else
                if a.val < 21 then
                  0
                else
                  0
            else
              if a.val < 24 then
                if a.val < 23 then
                  0
                else
                  0
              else
                if a.val < 25 then
                  0
                else
                  if a.val < 26 then
                    0
                  else
                    0
          else
            if a.val < 31 then
              if a.val < 29 then
                if a.val < 28 then
                  0
                else
                  0
              else
                if a.val < 30 then
                  0
                else
                  0
            else
              if a.val < 33 then
                if a.val < 32 then
                  0
                else
                  0
              else
                if a.val < 34 then
                  0
                else
                  if a.val < 35 then
                    0
                  else
                    0
      else
        if a.val < 54 then
          if a.val < 45 then
            if a.val < 40 then
              if a.val < 38 then
                if a.val < 37 then
                  0
                else
                  0
              else
                if a.val < 39 then
                  0
                else
                  0
            else
              if a.val < 42 then
                if a.val < 41 then
                  0
                else
                  0
              else
                if a.val < 43 then
                  0
                else
                  if a.val < 44 then
                    0
                  else
                    0
          else
            if a.val < 49 then
              if a.val < 47 then
                if a.val < 46 then
                  0
                else
                  0
              else
                if a.val < 48 then
                  0
                else
                  0
            else
              if a.val < 51 then
                if a.val < 50 then
                  0
                else
                  0
              else
                if a.val < 52 then
                  0
                else
                  if a.val < 53 then
                    0
                  else
                    0
        else
          if a.val < 63 then
            if a.val < 58 then
              if a.val < 56 then
                if a.val < 55 then
                  0
                else
                  0
              else
                if a.val < 57 then
                  0
                else
                  0
            else
              if a.val < 60 then
                if a.val < 59 then
                  0
                else
                  0
              else
                if a.val < 61 then
                  0
                else
                  if a.val < 62 then
                    0
                  else
                    0
          else
            if a.val < 67 then
              if a.val < 65 then
                if a.val < 64 then
                  0
                else
                  0
              else
                if a.val < 66 then
                  0
                else
                  0
            else
              if a.val < 69 then
                if a.val < 68 then
                  0
                else
                  0
              else
                if a.val < 70 then
                  0
                else
                  if a.val < 71 then
                    0
                  else
                    0
    else
      if a.val < 108 then
        if a.val < 90 then
          if a.val < 81 then
            if a.val < 76 then
              if a.val < 74 then
                if a.val < 73 then
                  0
                else
                  0
              else
                if a.val < 75 then
                  0
                else
                  0
            else
              if a.val < 78 then
                if a.val < 77 then
                  0
                else
                  0
              else
                if a.val < 79 then
                  0
                else
                  if a.val < 80 then
                    0
                  else
                    0
          else
            if a.val < 85 then
              if a.val < 83 then
                if a.val < 82 then
                  0
                else
                  0
              else
                if a.val < 84 then
                  0
                else
                  0
            else
              if a.val < 87 then
                if a.val < 86 then
                  0
                else
                  0
              else
                if a.val < 88 then
                  0
                else
                  if a.val < 89 then
                    0
                  else
                    0
        else
          if a.val < 99 then
            if a.val < 94 then
              if a.val < 92 then
                if a.val < 91 then
                  0
                else
                  0
              else
                if a.val < 93 then
                  0
                else
                  0
            else
              if a.val < 96 then
                if a.val < 95 then
                  0
                else
                  0
              else
                if a.val < 97 then
                  0
                else
                  if a.val < 98 then
                    0
                  else
                    0
          else
            if a.val < 103 then
              if a.val < 101 then
                if a.val < 100 then
                  0
                else
                  0
              else
                if a.val < 102 then
                  0
                else
                  0
            else
              if a.val < 105 then
                if a.val < 104 then
                  0
                else
                  0
              else
                if a.val < 106 then
                  0
                else
                  if a.val < 107 then
                    0
                  else
                    0
      else
        if a.val < 126 then
          if a.val < 117 then
            if a.val < 112 then
              if a.val < 110 then
                if a.val < 109 then
                  0
                else
                  0
              else
                if a.val < 111 then
                  0
                else
                  0
            else
              if a.val < 114 then
                if a.val < 113 then
                  0
                else
                  0
              else
                if a.val < 115 then
                  0
                else
                  if a.val < 116 then
                    0
                  else
                    0
          else
            if a.val < 121 then
              if a.val < 119 then
                if a.val < 118 then
                  0
                else
                  0
              else
                if a.val < 120 then
                  0
                else
                  0
            else
              if a.val < 123 then
                if a.val < 122 then
                  0
                else
                  0
              else
                if a.val < 124 then
                  0
                else
                  if a.val < 125 then
                    0
                  else
                    0
        else
          if a.val < 135 then
            if a.val < 130 then
              if a.val < 128 then
                if a.val < 127 then
                  0
                else
                  0
              else
                if a.val < 129 then
                  0
                else
                  0
            else
              if a.val < 132 then
                if a.val < 131 then
                  0
                else
                  0
              else
                if a.val < 133 then
                  0
                else
                  if a.val < 134 then
                    0
                  else
                    0
          else
            if a.val < 139 then
              if a.val < 137 then
                if a.val < 136 then
                  0
                else
                  0
              else
                if a.val < 138 then
                  0
                else
                  0
            else
              if a.val < 141 then
                if a.val < 140 then
                  0
                else
                  0
              else
                if a.val < 142 then
                  0
                else
                  if a.val < 143 then
                    0
                  else
                    0
  else
    if a.val < 216 then
      if a.val < 180 then
        if a.val < 162 then
          if a.val < 153 then
            if a.val < 148 then
              if a.val < 146 then
                if a.val < 145 then
                  0
                else
                  0
              else
                if a.val < 147 then
                  0
                else
                  0
            else
              if a.val < 150 then
                if a.val < 149 then
                  0
                else
                  0
              else
                if a.val < 151 then
                  0
                else
                  if a.val < 152 then
                    0
                  else
                    0
          else
            if a.val < 157 then
              if a.val < 155 then
                if a.val < 154 then
                  0
                else
                  0
              else
                if a.val < 156 then
                  0
                else
                  0
            else
              if a.val < 159 then
                if a.val < 158 then
                  0
                else
                  0
              else
                if a.val < 160 then
                  0
                else
                  if a.val < 161 then
                    0
                  else
                    0
        else
          if a.val < 171 then
            if a.val < 166 then
              if a.val < 164 then
                if a.val < 163 then
                  0
                else
                  0
              else
                if a.val < 165 then
                  0
                else
                  0
            else
              if a.val < 168 then
                if a.val < 167 then
                  0
                else
                  0
              else
                if a.val < 169 then
                  0
                else
                  if a.val < 170 then
                    0
                  else
                    0
          else
            if a.val < 175 then
              if a.val < 173 then
                if a.val < 172 then
                  0
                else
                  0
              else
                if a.val < 174 then
                  0
                else
                  0
            else
              if a.val < 177 then
                if a.val < 176 then
                  0
                else
                  0
              else
                if a.val < 178 then
                  0
                else
                  if a.val < 179 then
                    0
                  else
                    0
      else
        if a.val < 198 then
          if a.val < 189 then
            if a.val < 184 then
              if a.val < 182 then
                if a.val < 181 then
                  0
                else
                  0
              else
                if a.val < 183 then
                  0
                else
                  0
            else
              if a.val < 186 then
                if a.val < 185 then
                  0
                else
                  0
              else
                if a.val < 187 then
                  0
                else
                  if a.val < 188 then
                    0
                  else
                    0
          else
            if a.val < 193 then
              if a.val < 191 then
                if a.val < 190 then
                  0
                else
                  0
              else
                if a.val < 192 then
                  0
                else
                  0
            else
              if a.val < 195 then
                if a.val < 194 then
                  0
                else
                  0
              else
                if a.val < 196 then
                  0
                else
                  if a.val < 197 then
                    0
                  else
                    0
        else
          if a.val < 207 then
            if a.val < 202 then
              if a.val < 200 then
                if a.val < 199 then
                  0
                else
                  0
              else
                if a.val < 201 then
                  0
                else
                  0
            else
              if a.val < 204 then
                if a.val < 203 then
                  0
                else
                  0
              else
                if a.val < 205 then
                  0
                else
                  if a.val < 206 then
                    0
                  else
                    0
          else
            if a.val < 211 then
              if a.val < 209 then
                if a.val < 208 then
                  0
                else
                  0
              else
                if a.val < 210 then
                  0
                else
                  0
            else
              if a.val < 213 then
                if a.val < 212 then
                  0
                else
                  0
              else
                if a.val < 214 then
                  0
                else
                  if a.val < 215 then
                    0
                  else
                    0
    else
      if a.val < 252 then
        if a.val < 234 then
          if a.val < 225 then
            if a.val < 220 then
              if a.val < 218 then
                if a.val < 217 then
                  0
                else
                  0
              else
                if a.val < 219 then
                  0
                else
                  0
            else
              if a.val < 222 then
                if a.val < 221 then
                  0
                else
                  0
              else
                if a.val < 223 then
                  0
                else
                  if a.val < 224 then
                    0
                  else
                    0
          else
            if a.val < 229 then
              if a.val < 227 then
                if a.val < 226 then
                  0
                else
                  0
              else
                if a.val < 228 then
                  0
                else
                  0
            else
              if a.val < 231 then
                if a.val < 230 then
                  0
                else
                  0
              else
                if a.val < 232 then
                  0
                else
                  if a.val < 233 then
                    0
                  else
                    0
        else
          if a.val < 243 then
            if a.val < 238 then
              if a.val < 236 then
                if a.val < 235 then
                  0
                else
                  0
              else
                if a.val < 237 then
                  0
                else
                  0
            else
              if a.val < 240 then
                if a.val < 239 then
                  0
                else
                  0
              else
                if a.val < 241 then
                  0
                else
                  if a.val < 242 then
                    0
                  else
                    0
          else
            if a.val < 247 then
              if a.val < 245 then
                if a.val < 244 then
                  0
                else
                  0
              else
                if a.val < 246 then
                  0
                else
                  0
            else
              if a.val < 249 then
                if a.val < 248 then
                  0
                else
                  0
              else
                if a.val < 250 then
                  0
                else
                  if a.val < 251 then
                    0
                  else
                    0
      else
        if a.val < 270 then
          if a.val < 261 then
            if a.val < 256 then
              if a.val < 254 then
                if a.val < 253 then
                  0
                else
                  0
              else
                if a.val < 255 then
                  0
                else
                  0
            else
              if a.val < 258 then
                if a.val < 257 then
                  0
                else
                  0
              else
                if a.val < 259 then
                  0
                else
                  if a.val < 260 then
                    0
                  else
                    0
          else
            if a.val < 265 then
              if a.val < 263 then
                if a.val < 262 then
                  0
                else
                  0
              else
                if a.val < 264 then
                  0
                else
                  0
            else
              if a.val < 267 then
                if a.val < 266 then
                  0
                else
                  0
              else
                if a.val < 268 then
                  0
                else
                  if a.val < 269 then
                    0
                  else
                    0
        else
          if a.val < 279 then
            if a.val < 274 then
              if a.val < 272 then
                if a.val < 271 then
                  0
                else
                  0
              else
                if a.val < 273 then
                  2
                else
                  2
            else
              if a.val < 276 then
                if a.val < 275 then
                  2
                else
                  2
              else
                if a.val < 277 then
                  2
                else
                  if a.val < 278 then
                    2
                  else
                    2
          else
            if a.val < 283 then
              if a.val < 281 then
                if a.val < 280 then
                  2
                else
                  2
              else
                if a.val < 282 then
                  2
                else
                  2
            else
              if a.val < 285 then
                if a.val < 284 then
                  2
                else
                  2
              else
                if a.val < 286 then
                  2
                else
                  if a.val < 287 then
                    2
                  else
                    2
def flip0_3 (a : Fin 288) : Fin 288 :=
  if a.val < 144 then
    if a.val < 72 then
      if a.val < 36 then
        if a.val < 18 then
          if a.val < 9 then
            if a.val < 4 then
              if a.val < 2 then
                if a.val < 1 then
                  0
                else
                  2
              else
                if a.val < 3 then
                  1
                else
                  3
            else
              if a.val < 6 then
                if a.val < 5 then
                  4
                else
                  6
              else
                if a.val < 7 then
                  5
                else
                  if a.val < 8 then
                    7
                  else
                    8
          else
            if a.val < 13 then
              if a.val < 11 then
                if a.val < 10 then
                  10
                else
                  9
              else
                if a.val < 12 then
                  11
                else
                  12
            else
              if a.val < 15 then
                if a.val < 14 then
                  14
                else
                  13
              else
                if a.val < 16 then
                  15
                else
                  if a.val < 17 then
                    24
                  else
                    25
        else
          if a.val < 27 then
            if a.val < 22 then
              if a.val < 20 then
                if a.val < 19 then
                  26
                else
                  27
              else
                if a.val < 21 then
                  28
                else
                  29
            else
              if a.val < 24 then
                if a.val < 23 then
                  30
                else
                  31
              else
                if a.val < 25 then
                  16
                else
                  if a.val < 26 then
                    17
                  else
                    18
          else
            if a.val < 31 then
              if a.val < 29 then
                if a.val < 28 then
                  19
                else
                  20
              else
                if a.val < 30 then
                  21
                else
                  22
            else
              if a.val < 33 then
                if a.val < 32 then
                  23
                else
                  32
              else
                if a.val < 34 then
                  34
                else
                  if a.val < 35 then
                    33
                  else
                    35
      else
        if a.val < 54 then
          if a.val < 45 then
            if a.val < 40 then
              if a.val < 38 then
                if a.val < 37 then
                  36
                else
                  38
              else
                if a.val < 39 then
                  37
                else
                  39
            else
              if a.val < 42 then
                if a.val < 41 then
                  40
                else
                  42
              else
                if a.val < 43 then
                  41
                else
                  if a.val < 44 then
                    43
                  else
                    44
          else
            if a.val < 49 then
              if a.val < 47 then
                if a.val < 46 then
                  46
                else
                  45
              else
                if a.val < 48 then
                  47
                else
                  56
            else
              if a.val < 51 then
                if a.val < 50 then
                  57
                else
                  58
              else
                if a.val < 52 then
                  59
                else
                  if a.val < 53 then
                    60
                  else
                    61
        else
          if a.val < 63 then
            if a.val < 58 then
              if a.val < 56 then
                if a.val < 55 then
                  62
                else
                  63
              else
                if a.val < 57 then
                  48
                else
                  49
            else
              if a.val < 60 then
                if a.val < 59 then
                  50
                else
                  51
              else
                if a.val < 61 then
                  52
                else
                  if a.val < 62 then
                    53
                  else
                    54
          else
            if a.val < 67 then
              if a.val < 65 then
                if a.val < 64 then
                  55
                else
                  72
              else
                if a.val < 66 then
                  73
                else
                  74
            else
              if a.val < 69 then
                if a.val < 68 then
                  75
                else
                  76
              else
                if a.val < 70 then
                  77
                else
                  if a.val < 71 then
                    78
                  else
                    79
    else
      if a.val < 108 then
        if a.val < 90 then
          if a.val < 81 then
            if a.val < 76 then
              if a.val < 74 then
                if a.val < 73 then
                  64
                else
                  65
              else
                if a.val < 75 then
                  66
                else
                  67
            else
              if a.val < 78 then
                if a.val < 77 then
                  68
                else
                  69
              else
                if a.val < 79 then
                  70
                else
                  if a.val < 80 then
                    71
                  else
                    88
          else
            if a.val < 85 then
              if a.val < 83 then
                if a.val < 82 then
                  89
                else
                  90
              else
                if a.val < 84 then
                  91
                else
                  92
            else
              if a.val < 87 then
                if a.val < 86 then
                  93
                else
                  94
              else
                if a.val < 88 then
                  95
                else
                  if a.val < 89 then
                    80
                  else
                    81
        else
          if a.val < 99 then
            if a.val < 94 then
              if a.val < 92 then
                if a.val < 91 then
                  82
                else
                  83
              else
                if a.val < 93 then
                  84
                else
                  85
            else
              if a.val < 96 then
                if a.val < 95 then
                  86
                else
                  87
              else
                if a.val < 97 then
                  104
                else
                  if a.val < 98 then
                    105
                  else
                    106
          else
            if a.val < 103 then
              if a.val < 101 then
                if a.val < 100 then
                  107
                else
                  108
              else
                if a.val < 102 then
                  109
                else
                  110
            else
              if a.val < 105 then
                if a.val < 104 then
                  111
                else
                  96
              else
                if a.val < 106 then
                  97
                else
                  if a.val < 107 then
                    98
                  else
                    99
      else
        if a.val < 126 then
          if a.val < 117 then
            if a.val < 112 then
              if a.val < 110 then
                if a.val < 109 then
                  100
                else
                  101
              else
                if a.val < 111 then
                  102
                else
                  103
            else
              if a.val < 114 then
                if a.val < 113 then
                  120
                else
                  121
              else
                if a.val < 115 then
                  122
                else
                  if a.val < 116 then
                    123
                  else
                    124
          else
            if a.val < 121 then
              if a.val < 119 then
                if a.val < 118 then
                  125
                else
                  126
              else
                if a.val < 120 then
                  127
                else
                  112
            else
              if a.val < 123 then
                if a.val < 122 then
                  113
                else
                  114
              else
                if a.val < 124 then
                  115
                else
                  if a.val < 125 then
                    116
                  else
                    117
        else
          if a.val < 135 then
            if a.val < 130 then
              if a.val < 128 then
                if a.val < 127 then
                  118
                else
                  119
              else
                if a.val < 129 then
                  136
                else
                  137
            else
              if a.val < 132 then
                if a.val < 131 then
                  138
                else
                  139
              else
                if a.val < 133 then
                  140
                else
                  if a.val < 134 then
                    141
                  else
                    142
          else
            if a.val < 139 then
              if a.val < 137 then
                if a.val < 136 then
                  143
                else
                  128
              else
                if a.val < 138 then
                  129
                else
                  130
            else
              if a.val < 141 then
                if a.val < 140 then
                  131
                else
                  132
              else
                if a.val < 142 then
                  133
                else
                  if a.val < 143 then
                    134
                  else
                    135
  else
    if a.val < 216 then
      if a.val < 180 then
        if a.val < 162 then
          if a.val < 153 then
            if a.val < 148 then
              if a.val < 146 then
                if a.val < 145 then
                  152
                else
                  153
              else
                if a.val < 147 then
                  154
                else
                  155
            else
              if a.val < 150 then
                if a.val < 149 then
                  156
                else
                  157
              else
                if a.val < 151 then
                  158
                else
                  if a.val < 152 then
                    159
                  else
                    144
          else
            if a.val < 157 then
              if a.val < 155 then
                if a.val < 154 then
                  145
                else
                  146
              else
                if a.val < 156 then
                  147
                else
                  148
            else
              if a.val < 159 then
                if a.val < 158 then
                  149
                else
                  150
              else
                if a.val < 160 then
                  151
                else
                  if a.val < 161 then
                    168
                  else
                    169
        else
          if a.val < 171 then
            if a.val < 166 then
              if a.val < 164 then
                if a.val < 163 then
                  170
                else
                  171
              else
                if a.val < 165 then
                  172
                else
                  173
            else
              if a.val < 168 then
                if a.val < 167 then
                  174
                else
                  175
              else
                if a.val < 169 then
                  160
                else
                  if a.val < 170 then
                    161
                  else
                    162
          else
            if a.val < 175 then
              if a.val < 173 then
                if a.val < 172 then
                  163
                else
                  164
              else
                if a.val < 174 then
                  165
                else
                  166
            else
              if a.val < 177 then
                if a.val < 176 then
                  167
                else
                  184
              else
                if a.val < 178 then
                  185
                else
                  if a.val < 179 then
                    186
                  else
                    187
      else
        if a.val < 198 then
          if a.val < 189 then
            if a.val < 184 then
              if a.val < 182 then
                if a.val < 181 then
                  188
                else
                  189
              else
                if a.val < 183 then
                  190
                else
                  191
            else
              if a.val < 186 then
                if a.val < 185 then
                  176
                else
                  177
              else
                if a.val < 187 then
                  178
                else
                  if a.val < 188 then
                    179
                  else
                    180
          else
            if a.val < 193 then
              if a.val < 191 then
                if a.val < 190 then
                  181
                else
                  182
              else
                if a.val < 192 then
                  183
                else
                  200
            else
              if a.val < 195 then
                if a.val < 194 then
                  201
                else
                  202
              else
                if a.val < 196 then
                  203
                else
                  if a.val < 197 then
                    204
                  else
                    205
        else
          if a.val < 207 then
            if a.val < 202 then
              if a.val < 200 then
                if a.val < 199 then
                  206
                else
                  207
              else
                if a.val < 201 then
                  192
                else
                  193
            else
              if a.val < 204 then
                if a.val < 203 then
                  194
                else
                  195
              else
                if a.val < 205 then
                  196
                else
                  if a.val < 206 then
                    197
                  else
                    198
          else
            if a.val < 211 then
              if a.val < 209 then
                if a.val < 208 then
                  199
                else
                  216
              else
                if a.val < 210 then
                  217
                else
                  218
            else
              if a.val < 213 then
                if a.val < 212 then
                  219
                else
                  220
              else
                if a.val < 214 then
                  221
                else
                  if a.val < 215 then
                    222
                  else
                    223
    else
      if a.val < 252 then
        if a.val < 234 then
          if a.val < 225 then
            if a.val < 220 then
              if a.val < 218 then
                if a.val < 217 then
                  208
                else
                  209
              else
                if a.val < 219 then
                  210
                else
                  211
            else
              if a.val < 222 then
                if a.val < 221 then
                  212
                else
                  213
              else
                if a.val < 223 then
                  214
                else
                  if a.val < 224 then
                    215
                  else
                    232
          else
            if a.val < 229 then
              if a.val < 227 then
                if a.val < 226 then
                  233
                else
                  234
              else
                if a.val < 228 then
                  235
                else
                  236
            else
              if a.val < 231 then
                if a.val < 230 then
                  237
                else
                  238
              else
                if a.val < 232 then
                  239
                else
                  if a.val < 233 then
                    224
                  else
                    225
        else
          if a.val < 243 then
            if a.val < 238 then
              if a.val < 236 then
                if a.val < 235 then
                  226
                else
                  227
              else
                if a.val < 237 then
                  228
                else
                  229
            else
              if a.val < 240 then
                if a.val < 239 then
                  230
                else
                  231
              else
                if a.val < 241 then
                  240
                else
                  if a.val < 242 then
                    242
                  else
                    241
          else
            if a.val < 247 then
              if a.val < 245 then
                if a.val < 244 then
                  243
                else
                  244
              else
                if a.val < 246 then
                  246
                else
                  245
            else
              if a.val < 249 then
                if a.val < 248 then
                  247
                else
                  256
              else
                if a.val < 250 then
                  257
                else
                  if a.val < 251 then
                    258
                  else
                    259
      else
        if a.val < 270 then
          if a.val < 261 then
            if a.val < 256 then
              if a.val < 254 then
                if a.val < 253 then
                  260
                else
                  261
              else
                if a.val < 255 then
                  262
                else
                  263
            else
              if a.val < 258 then
                if a.val < 257 then
                  248
                else
                  249
              else
                if a.val < 259 then
                  250
                else
                  if a.val < 260 then
                    251
                  else
                    252
          else
            if a.val < 265 then
              if a.val < 263 then
                if a.val < 262 then
                  253
                else
                  254
              else
                if a.val < 264 then
                  255
                else
                  264
            else
              if a.val < 267 then
                if a.val < 266 then
                  266
                else
                  265
              else
                if a.val < 268 then
                  267
                else
                  if a.val < 269 then
                    268
                  else
                    270
        else
          if a.val < 279 then
            if a.val < 274 then
              if a.val < 272 then
                if a.val < 271 then
                  269
                else
                  271
              else
                if a.val < 273 then
                  280
                else
                  281
            else
              if a.val < 276 then
                if a.val < 275 then
                  282
                else
                  283
              else
                if a.val < 277 then
                  284
                else
                  if a.val < 278 then
                    285
                  else
                    286
          else
            if a.val < 283 then
              if a.val < 281 then
                if a.val < 280 then
                  287
                else
                  272
              else
                if a.val < 282 then
                  273
                else
                  274
            else
              if a.val < 285 then
                if a.val < 284 then
                  275
                else
                  276
              else
                if a.val < 286 then
                  277
                else
                  if a.val < 287 then
                    278
                  else
                    279
def phase0_3 (a : Fin 288) : Fin 4 :=
  if a.val < 144 then
    if a.val < 72 then
      if a.val < 36 then
        if a.val < 18 then
          if a.val < 9 then
            if a.val < 4 then
              if a.val < 2 then
                if a.val < 1 then
                  0
                else
                  0
              else
                if a.val < 3 then
                  0
                else
                  0
            else
              if a.val < 6 then
                if a.val < 5 then
                  0
                else
                  0
              else
                if a.val < 7 then
                  0
                else
                  if a.val < 8 then
                    0
                  else
                    0
          else
            if a.val < 13 then
              if a.val < 11 then
                if a.val < 10 then
                  0
                else
                  0
              else
                if a.val < 12 then
                  0
                else
                  0
            else
              if a.val < 15 then
                if a.val < 14 then
                  0
                else
                  0
              else
                if a.val < 16 then
                  0
                else
                  if a.val < 17 then
                    0
                  else
                    0
        else
          if a.val < 27 then
            if a.val < 22 then
              if a.val < 20 then
                if a.val < 19 then
                  0
                else
                  0
              else
                if a.val < 21 then
                  0
                else
                  0
            else
              if a.val < 24 then
                if a.val < 23 then
                  0
                else
                  0
              else
                if a.val < 25 then
                  0
                else
                  if a.val < 26 then
                    0
                  else
                    0
          else
            if a.val < 31 then
              if a.val < 29 then
                if a.val < 28 then
                  0
                else
                  0
              else
                if a.val < 30 then
                  0
                else
                  0
            else
              if a.val < 33 then
                if a.val < 32 then
                  0
                else
                  0
              else
                if a.val < 34 then
                  0
                else
                  if a.val < 35 then
                    0
                  else
                    0
      else
        if a.val < 54 then
          if a.val < 45 then
            if a.val < 40 then
              if a.val < 38 then
                if a.val < 37 then
                  0
                else
                  0
              else
                if a.val < 39 then
                  0
                else
                  0
            else
              if a.val < 42 then
                if a.val < 41 then
                  0
                else
                  0
              else
                if a.val < 43 then
                  0
                else
                  if a.val < 44 then
                    0
                  else
                    0
          else
            if a.val < 49 then
              if a.val < 47 then
                if a.val < 46 then
                  0
                else
                  0
              else
                if a.val < 48 then
                  0
                else
                  0
            else
              if a.val < 51 then
                if a.val < 50 then
                  0
                else
                  0
              else
                if a.val < 52 then
                  0
                else
                  if a.val < 53 then
                    0
                  else
                    0
        else
          if a.val < 63 then
            if a.val < 58 then
              if a.val < 56 then
                if a.val < 55 then
                  0
                else
                  0
              else
                if a.val < 57 then
                  0
                else
                  0
            else
              if a.val < 60 then
                if a.val < 59 then
                  0
                else
                  0
              else
                if a.val < 61 then
                  0
                else
                  if a.val < 62 then
                    0
                  else
                    0
          else
            if a.val < 67 then
              if a.val < 65 then
                if a.val < 64 then
                  0
                else
                  0
              else
                if a.val < 66 then
                  0
                else
                  0
            else
              if a.val < 69 then
                if a.val < 68 then
                  0
                else
                  0
              else
                if a.val < 70 then
                  0
                else
                  if a.val < 71 then
                    0
                  else
                    0
    else
      if a.val < 108 then
        if a.val < 90 then
          if a.val < 81 then
            if a.val < 76 then
              if a.val < 74 then
                if a.val < 73 then
                  0
                else
                  0
              else
                if a.val < 75 then
                  0
                else
                  0
            else
              if a.val < 78 then
                if a.val < 77 then
                  0
                else
                  0
              else
                if a.val < 79 then
                  0
                else
                  if a.val < 80 then
                    0
                  else
                    0
          else
            if a.val < 85 then
              if a.val < 83 then
                if a.val < 82 then
                  0
                else
                  0
              else
                if a.val < 84 then
                  0
                else
                  0
            else
              if a.val < 87 then
                if a.val < 86 then
                  0
                else
                  0
              else
                if a.val < 88 then
                  0
                else
                  if a.val < 89 then
                    0
                  else
                    0
        else
          if a.val < 99 then
            if a.val < 94 then
              if a.val < 92 then
                if a.val < 91 then
                  0
                else
                  0
              else
                if a.val < 93 then
                  0
                else
                  0
            else
              if a.val < 96 then
                if a.val < 95 then
                  0
                else
                  0
              else
                if a.val < 97 then
                  0
                else
                  if a.val < 98 then
                    0
                  else
                    0
          else
            if a.val < 103 then
              if a.val < 101 then
                if a.val < 100 then
                  0
                else
                  0
              else
                if a.val < 102 then
                  0
                else
                  0
            else
              if a.val < 105 then
                if a.val < 104 then
                  0
                else
                  0
              else
                if a.val < 106 then
                  0
                else
                  if a.val < 107 then
                    0
                  else
                    0
      else
        if a.val < 126 then
          if a.val < 117 then
            if a.val < 112 then
              if a.val < 110 then
                if a.val < 109 then
                  0
                else
                  0
              else
                if a.val < 111 then
                  0
                else
                  0
            else
              if a.val < 114 then
                if a.val < 113 then
                  0
                else
                  0
              else
                if a.val < 115 then
                  0
                else
                  if a.val < 116 then
                    0
                  else
                    0
          else
            if a.val < 121 then
              if a.val < 119 then
                if a.val < 118 then
                  0
                else
                  0
              else
                if a.val < 120 then
                  0
                else
                  0
            else
              if a.val < 123 then
                if a.val < 122 then
                  0
                else
                  0
              else
                if a.val < 124 then
                  0
                else
                  if a.val < 125 then
                    0
                  else
                    0
        else
          if a.val < 135 then
            if a.val < 130 then
              if a.val < 128 then
                if a.val < 127 then
                  0
                else
                  0
              else
                if a.val < 129 then
                  0
                else
                  0
            else
              if a.val < 132 then
                if a.val < 131 then
                  0
                else
                  0
              else
                if a.val < 133 then
                  0
                else
                  if a.val < 134 then
                    0
                  else
                    0
          else
            if a.val < 139 then
              if a.val < 137 then
                if a.val < 136 then
                  0
                else
                  0
              else
                if a.val < 138 then
                  0
                else
                  0
            else
              if a.val < 141 then
                if a.val < 140 then
                  0
                else
                  0
              else
                if a.val < 142 then
                  0
                else
                  if a.val < 143 then
                    0
                  else
                    0
  else
    if a.val < 216 then
      if a.val < 180 then
        if a.val < 162 then
          if a.val < 153 then
            if a.val < 148 then
              if a.val < 146 then
                if a.val < 145 then
                  0
                else
                  0
              else
                if a.val < 147 then
                  0
                else
                  0
            else
              if a.val < 150 then
                if a.val < 149 then
                  0
                else
                  0
              else
                if a.val < 151 then
                  0
                else
                  if a.val < 152 then
                    0
                  else
                    0
          else
            if a.val < 157 then
              if a.val < 155 then
                if a.val < 154 then
                  0
                else
                  0
              else
                if a.val < 156 then
                  0
                else
                  0
            else
              if a.val < 159 then
                if a.val < 158 then
                  0
                else
                  0
              else
                if a.val < 160 then
                  0
                else
                  if a.val < 161 then
                    0
                  else
                    0
        else
          if a.val < 171 then
            if a.val < 166 then
              if a.val < 164 then
                if a.val < 163 then
                  0
                else
                  0
              else
                if a.val < 165 then
                  0
                else
                  0
            else
              if a.val < 168 then
                if a.val < 167 then
                  0
                else
                  0
              else
                if a.val < 169 then
                  0
                else
                  if a.val < 170 then
                    0
                  else
                    0
          else
            if a.val < 175 then
              if a.val < 173 then
                if a.val < 172 then
                  0
                else
                  0
              else
                if a.val < 174 then
                  0
                else
                  0
            else
              if a.val < 177 then
                if a.val < 176 then
                  0
                else
                  0
              else
                if a.val < 178 then
                  0
                else
                  if a.val < 179 then
                    0
                  else
                    0
      else
        if a.val < 198 then
          if a.val < 189 then
            if a.val < 184 then
              if a.val < 182 then
                if a.val < 181 then
                  0
                else
                  0
              else
                if a.val < 183 then
                  0
                else
                  0
            else
              if a.val < 186 then
                if a.val < 185 then
                  0
                else
                  0
              else
                if a.val < 187 then
                  0
                else
                  if a.val < 188 then
                    0
                  else
                    0
          else
            if a.val < 193 then
              if a.val < 191 then
                if a.val < 190 then
                  0
                else
                  0
              else
                if a.val < 192 then
                  0
                else
                  0
            else
              if a.val < 195 then
                if a.val < 194 then
                  0
                else
                  0
              else
                if a.val < 196 then
                  0
                else
                  if a.val < 197 then
                    0
                  else
                    0
        else
          if a.val < 207 then
            if a.val < 202 then
              if a.val < 200 then
                if a.val < 199 then
                  0
                else
                  0
              else
                if a.val < 201 then
                  0
                else
                  0
            else
              if a.val < 204 then
                if a.val < 203 then
                  0
                else
                  0
              else
                if a.val < 205 then
                  0
                else
                  if a.val < 206 then
                    0
                  else
                    0
          else
            if a.val < 211 then
              if a.val < 209 then
                if a.val < 208 then
                  0
                else
                  0
              else
                if a.val < 210 then
                  0
                else
                  0
            else
              if a.val < 213 then
                if a.val < 212 then
                  0
                else
                  0
              else
                if a.val < 214 then
                  0
                else
                  if a.val < 215 then
                    0
                  else
                    0
    else
      if a.val < 252 then
        if a.val < 234 then
          if a.val < 225 then
            if a.val < 220 then
              if a.val < 218 then
                if a.val < 217 then
                  0
                else
                  0
              else
                if a.val < 219 then
                  0
                else
                  0
            else
              if a.val < 222 then
                if a.val < 221 then
                  0
                else
                  0
              else
                if a.val < 223 then
                  0
                else
                  if a.val < 224 then
                    0
                  else
                    0
          else
            if a.val < 229 then
              if a.val < 227 then
                if a.val < 226 then
                  0
                else
                  0
              else
                if a.val < 228 then
                  0
                else
                  0
            else
              if a.val < 231 then
                if a.val < 230 then
                  0
                else
                  0
              else
                if a.val < 232 then
                  0
                else
                  if a.val < 233 then
                    0
                  else
                    0
        else
          if a.val < 243 then
            if a.val < 238 then
              if a.val < 236 then
                if a.val < 235 then
                  0
                else
                  0
              else
                if a.val < 237 then
                  0
                else
                  0
            else
              if a.val < 240 then
                if a.val < 239 then
                  0
                else
                  0
              else
                if a.val < 241 then
                  0
                else
                  if a.val < 242 then
                    0
                  else
                    0
          else
            if a.val < 247 then
              if a.val < 245 then
                if a.val < 244 then
                  0
                else
                  0
              else
                if a.val < 246 then
                  0
                else
                  0
            else
              if a.val < 249 then
                if a.val < 248 then
                  0
                else
                  0
              else
                if a.val < 250 then
                  0
                else
                  if a.val < 251 then
                    0
                  else
                    0
      else
        if a.val < 270 then
          if a.val < 261 then
            if a.val < 256 then
              if a.val < 254 then
                if a.val < 253 then
                  0
                else
                  0
              else
                if a.val < 255 then
                  0
                else
                  0
            else
              if a.val < 258 then
                if a.val < 257 then
                  0
                else
                  0
              else
                if a.val < 259 then
                  0
                else
                  if a.val < 260 then
                    0
                  else
                    0
          else
            if a.val < 265 then
              if a.val < 263 then
                if a.val < 262 then
                  0
                else
                  0
              else
                if a.val < 264 then
                  0
                else
                  0
            else
              if a.val < 267 then
                if a.val < 266 then
                  0
                else
                  0
              else
                if a.val < 268 then
                  0
                else
                  if a.val < 269 then
                    0
                  else
                    0
        else
          if a.val < 279 then
            if a.val < 274 then
              if a.val < 272 then
                if a.val < 271 then
                  0
                else
                  0
              else
                if a.val < 273 then
                  0
                else
                  0
            else
              if a.val < 276 then
                if a.val < 275 then
                  0
                else
                  0
              else
                if a.val < 277 then
                  0
                else
                  if a.val < 278 then
                    0
                  else
                    0
          else
            if a.val < 283 then
              if a.val < 281 then
                if a.val < 280 then
                  0
                else
                  0
              else
                if a.val < 282 then
                  0
                else
                  0
            else
              if a.val < 285 then
                if a.val < 284 then
                  0
                else
                  0
              else
                if a.val < 286 then
                  0
                else
                  if a.val < 287 then
                    0
                  else
                    0
def flip1_0 (a : Fin 72) : Fin 72 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              10
            else
              11
          else
            if a.val < 3 then
              8
            else
              9
        else
          if a.val < 6 then
            if a.val < 5 then
              6
            else
              7
          else
            if a.val < 7 then
              4
            else
              if a.val < 8 then
                5
              else
                2
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              3
            else
              0
          else
            if a.val < 12 then
              1
            else
              58
        else
          if a.val < 15 then
            if a.val < 14 then
              59
            else
              56
          else
            if a.val < 16 then
              57
            else
              if a.val < 17 then
                54
              else
                55
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            if a.val < 19 then
              52
            else
              53
          else
            if a.val < 21 then
              50
            else
              51
        else
          if a.val < 24 then
            if a.val < 23 then
              48
            else
              49
          else
            if a.val < 25 then
              46
            else
              if a.val < 26 then
                47
              else
                44
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              45
            else
              42
          else
            if a.val < 30 then
              43
            else
              40
        else
          if a.val < 33 then
            if a.val < 32 then
              41
            else
              38
          else
            if a.val < 34 then
              39
            else
              if a.val < 35 then
                36
              else
                37
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          if a.val < 38 then
            if a.val < 37 then
              34
            else
              35
          else
            if a.val < 39 then
              32
            else
              33
        else
          if a.val < 42 then
            if a.val < 41 then
              30
            else
              31
          else
            if a.val < 43 then
              28
            else
              if a.val < 44 then
                29
              else
                26
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              27
            else
              24
          else
            if a.val < 48 then
              25
            else
              22
        else
          if a.val < 51 then
            if a.val < 50 then
              23
            else
              20
          else
            if a.val < 52 then
              21
            else
              if a.val < 53 then
                18
              else
                19
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            if a.val < 55 then
              16
            else
              17
          else
            if a.val < 57 then
              14
            else
              15
        else
          if a.val < 60 then
            if a.val < 59 then
              12
            else
              13
          else
            if a.val < 61 then
              60
            else
              if a.val < 62 then
                61
              else
                62
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              63
            else
              64
          else
            if a.val < 66 then
              65
            else
              66
        else
          if a.val < 69 then
            if a.val < 68 then
              67
            else
              68
          else
            if a.val < 70 then
              69
            else
              if a.val < 71 then
                70
              else
                71
def phase1_0 (a : Fin 72) : Fin 4 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              2
            else
              2
          else
            if a.val < 3 then
              2
            else
              2
        else
          if a.val < 6 then
            if a.val < 5 then
              2
            else
              2
          else
            if a.val < 7 then
              2
            else
              if a.val < 8 then
                2
              else
                2
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              2
            else
              2
          else
            if a.val < 12 then
              2
            else
              2
        else
          if a.val < 15 then
            if a.val < 14 then
              2
            else
              2
          else
            if a.val < 16 then
              2
            else
              if a.val < 17 then
                2
              else
                2
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            if a.val < 19 then
              2
            else
              2
          else
            if a.val < 21 then
              2
            else
              2
        else
          if a.val < 24 then
            if a.val < 23 then
              2
            else
              2
          else
            if a.val < 25 then
              2
            else
              if a.val < 26 then
                2
              else
                2
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              2
            else
              2
          else
            if a.val < 30 then
              2
            else
              2
        else
          if a.val < 33 then
            if a.val < 32 then
              2
            else
              2
          else
            if a.val < 34 then
              2
            else
              if a.val < 35 then
                2
              else
                2
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          if a.val < 38 then
            if a.val < 37 then
              2
            else
              2
          else
            if a.val < 39 then
              2
            else
              2
        else
          if a.val < 42 then
            if a.val < 41 then
              2
            else
              2
          else
            if a.val < 43 then
              2
            else
              if a.val < 44 then
                2
              else
                2
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              2
            else
              2
          else
            if a.val < 48 then
              2
            else
              2
        else
          if a.val < 51 then
            if a.val < 50 then
              2
            else
              2
          else
            if a.val < 52 then
              2
            else
              if a.val < 53 then
                2
              else
                2
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            if a.val < 55 then
              2
            else
              2
          else
            if a.val < 57 then
              2
            else
              2
        else
          if a.val < 60 then
            if a.val < 59 then
              2
            else
              2
          else
            if a.val < 61 then
              0
            else
              if a.val < 62 then
                0
              else
                0
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              0
            else
              0
          else
            if a.val < 66 then
              0
            else
              0
        else
          if a.val < 69 then
            if a.val < 68 then
              0
            else
              0
          else
            if a.val < 70 then
              0
            else
              if a.val < 71 then
                0
              else
                0
def flip1_1 (a : Fin 72) : Fin 72 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              10
            else
              11
          else
            if a.val < 3 then
              2
            else
              3
        else
          if a.val < 6 then
            if a.val < 5 then
              4
            else
              5
          else
            if a.val < 7 then
              6
            else
              if a.val < 8 then
                7
              else
                8
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              9
            else
              0
          else
            if a.val < 12 then
              1
            else
              44
        else
          if a.val < 15 then
            if a.val < 14 then
              45
            else
              46
          else
            if a.val < 16 then
              47
            else
              if a.val < 17 then
                48
              else
                49
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            if a.val < 19 then
              50
            else
              51
          else
            if a.val < 21 then
              52
            else
              53
        else
          if a.val < 24 then
            if a.val < 23 then
              54
            else
              55
          else
            if a.val < 25 then
              56
            else
              if a.val < 26 then
                57
              else
                58
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              59
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
                12
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              13
            else
              14
          else
            if a.val < 48 then
              15
            else
              16
        else
          if a.val < 51 then
            if a.val < 50 then
              17
            else
              18
          else
            if a.val < 52 then
              19
            else
              if a.val < 53 then
                20
              else
                21
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            if a.val < 55 then
              22
            else
              23
          else
            if a.val < 57 then
              24
            else
              25
        else
          if a.val < 60 then
            if a.val < 59 then
              26
            else
              27
          else
            if a.val < 61 then
              66
            else
              if a.val < 62 then
                67
              else
                64
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              65
            else
              62
          else
            if a.val < 66 then
              63
            else
              60
        else
          if a.val < 69 then
            if a.val < 68 then
              61
            else
              68
          else
            if a.val < 70 then
              69
            else
              if a.val < 71 then
                70
              else
                71
def phase1_1 (a : Fin 72) : Fin 4 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              0
            else
              0
          else
            if a.val < 3 then
              0
            else
              0
        else
          if a.val < 6 then
            if a.val < 5 then
              0
            else
              0
          else
            if a.val < 7 then
              0
            else
              if a.val < 8 then
                0
              else
                0
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              0
            else
              0
          else
            if a.val < 12 then
              0
            else
              0
        else
          if a.val < 15 then
            if a.val < 14 then
              0
            else
              0
          else
            if a.val < 16 then
              0
            else
              if a.val < 17 then
                0
              else
                0
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            if a.val < 19 then
              0
            else
              0
          else
            if a.val < 21 then
              0
            else
              0
        else
          if a.val < 24 then
            if a.val < 23 then
              0
            else
              0
          else
            if a.val < 25 then
              0
            else
              if a.val < 26 then
                0
              else
                0
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              0
            else
              0
          else
            if a.val < 30 then
              0
            else
              0
        else
          if a.val < 33 then
            if a.val < 32 then
              0
            else
              0
          else
            if a.val < 34 then
              0
            else
              if a.val < 35 then
                0
              else
                0
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          if a.val < 38 then
            if a.val < 37 then
              0
            else
              0
          else
            if a.val < 39 then
              0
            else
              0
        else
          if a.val < 42 then
            if a.val < 41 then
              0
            else
              0
          else
            if a.val < 43 then
              0
            else
              if a.val < 44 then
                0
              else
                0
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              0
            else
              0
          else
            if a.val < 48 then
              0
            else
              0
        else
          if a.val < 51 then
            if a.val < 50 then
              0
            else
              0
          else
            if a.val < 52 then
              0
            else
              if a.val < 53 then
                0
              else
                0
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            if a.val < 55 then
              0
            else
              0
          else
            if a.val < 57 then
              0
            else
              0
        else
          if a.val < 60 then
            if a.val < 59 then
              0
            else
              0
          else
            if a.val < 61 then
              2
            else
              if a.val < 62 then
                2
              else
                2
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              2
            else
              2
          else
            if a.val < 66 then
              2
            else
              2
        else
          if a.val < 69 then
            if a.val < 68 then
              2
            else
              0
          else
            if a.val < 70 then
              0
            else
              if a.val < 71 then
                0
              else
                0
def flip1_2 (a : Fin 72) : Fin 72 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              0
            else
              1
          else
            if a.val < 3 then
              8
            else
              9
        else
          if a.val < 6 then
            if a.val < 5 then
              4
            else
              5
          else
            if a.val < 7 then
              6
            else
              if a.val < 8 then
                7
              else
                2
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              3
            else
              10
          else
            if a.val < 12 then
              11
            else
              24
        else
          if a.val < 15 then
            if a.val < 14 then
              25
            else
              26
          else
            if a.val < 16 then
              27
            else
              if a.val < 17 then
                20
              else
                21
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            if a.val < 19 then
              22
            else
              23
          else
            if a.val < 21 then
              16
            else
              17
        else
          if a.val < 24 then
            if a.val < 23 then
              18
            else
              19
          else
            if a.val < 25 then
              12
            else
              if a.val < 26 then
                13
              else
                14
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              15
            else
              32
          else
            if a.val < 30 then
              33
            else
              34
        else
          if a.val < 33 then
            if a.val < 32 then
              35
            else
              28
          else
            if a.val < 34 then
              29
            else
              if a.val < 35 then
                30
              else
                31
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          if a.val < 38 then
            if a.val < 37 then
              40
            else
              41
          else
            if a.val < 39 then
              42
            else
              43
        else
          if a.val < 42 then
            if a.val < 41 then
              36
            else
              37
          else
            if a.val < 43 then
              38
            else
              if a.val < 44 then
                39
              else
                56
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              57
            else
              58
          else
            if a.val < 48 then
              59
            else
              52
        else
          if a.val < 51 then
            if a.val < 50 then
              53
            else
              54
          else
            if a.val < 52 then
              55
            else
              if a.val < 53 then
                48
              else
                49
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            if a.val < 55 then
              50
            else
              51
          else
            if a.val < 57 then
              44
            else
              45
        else
          if a.val < 60 then
            if a.val < 59 then
              46
            else
              47
          else
            if a.val < 61 then
              66
            else
              if a.val < 62 then
                67
              else
                62
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              63
            else
              64
          else
            if a.val < 66 then
              65
            else
              60
        else
          if a.val < 69 then
            if a.val < 68 then
              61
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
def phase1_2 (a : Fin 72) : Fin 4 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              0
            else
              0
          else
            if a.val < 3 then
              0
            else
              0
        else
          if a.val < 6 then
            if a.val < 5 then
              0
            else
              0
          else
            if a.val < 7 then
              0
            else
              if a.val < 8 then
                0
              else
                0
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              0
            else
              0
          else
            if a.val < 12 then
              0
            else
              0
        else
          if a.val < 15 then
            if a.val < 14 then
              0
            else
              0
          else
            if a.val < 16 then
              0
            else
              if a.val < 17 then
                0
              else
                0
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            if a.val < 19 then
              0
            else
              0
          else
            if a.val < 21 then
              0
            else
              0
        else
          if a.val < 24 then
            if a.val < 23 then
              0
            else
              0
          else
            if a.val < 25 then
              0
            else
              if a.val < 26 then
                0
              else
                0
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              0
            else
              0
          else
            if a.val < 30 then
              0
            else
              0
        else
          if a.val < 33 then
            if a.val < 32 then
              0
            else
              0
          else
            if a.val < 34 then
              0
            else
              if a.val < 35 then
                0
              else
                0
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          if a.val < 38 then
            if a.val < 37 then
              0
            else
              0
          else
            if a.val < 39 then
              0
            else
              0
        else
          if a.val < 42 then
            if a.val < 41 then
              0
            else
              0
          else
            if a.val < 43 then
              0
            else
              if a.val < 44 then
                0
              else
                0
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              0
            else
              0
          else
            if a.val < 48 then
              0
            else
              0
        else
          if a.val < 51 then
            if a.val < 50 then
              0
            else
              0
          else
            if a.val < 52 then
              0
            else
              if a.val < 53 then
                0
              else
                0
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            if a.val < 55 then
              0
            else
              0
          else
            if a.val < 57 then
              0
            else
              0
        else
          if a.val < 60 then
            if a.val < 59 then
              0
            else
              0
          else
            if a.val < 61 then
              0
            else
              if a.val < 62 then
                0
              else
                0
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              0
            else
              0
          else
            if a.val < 66 then
              0
            else
              0
        else
          if a.val < 69 then
            if a.val < 68 then
              0
            else
              2
          else
            if a.val < 70 then
              2
            else
              if a.val < 71 then
                2
              else
                2
def flip1_3 (a : Fin 72) : Fin 72 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              0
            else
              1
          else
            if a.val < 3 then
              2
            else
              3
        else
          if a.val < 6 then
            if a.val < 5 then
              6
            else
              7
          else
            if a.val < 7 then
              4
            else
              if a.val < 8 then
                5
              else
                8
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              9
            else
              10
          else
            if a.val < 12 then
              11
            else
              14
        else
          if a.val < 15 then
            if a.val < 14 then
              15
            else
              12
          else
            if a.val < 16 then
              13
            else
              if a.val < 17 then
                18
              else
                19
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            if a.val < 19 then
              16
            else
              17
          else
            if a.val < 21 then
              22
            else
              23
        else
          if a.val < 24 then
            if a.val < 23 then
              20
            else
              21
          else
            if a.val < 25 then
              26
            else
              if a.val < 26 then
                27
              else
                24
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              25
            else
              30
          else
            if a.val < 30 then
              31
            else
              28
        else
          if a.val < 33 then
            if a.val < 32 then
              29
            else
              34
          else
            if a.val < 34 then
              35
            else
              if a.val < 35 then
                32
              else
                33
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          if a.val < 38 then
            if a.val < 37 then
              38
            else
              39
          else
            if a.val < 39 then
              36
            else
              37
        else
          if a.val < 42 then
            if a.val < 41 then
              42
            else
              43
          else
            if a.val < 43 then
              40
            else
              if a.val < 44 then
                41
              else
                46
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              47
            else
              44
          else
            if a.val < 48 then
              45
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
              58
            else
              59
        else
          if a.val < 60 then
            if a.val < 59 then
              56
            else
              57
          else
            if a.val < 61 then
              60
            else
              if a.val < 62 then
                61
              else
                64
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              65
            else
              62
          else
            if a.val < 66 then
              63
            else
              66
        else
          if a.val < 69 then
            if a.val < 68 then
              67
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
def phase1_3 (a : Fin 72) : Fin 4 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              0
            else
              0
          else
            if a.val < 3 then
              0
            else
              0
        else
          if a.val < 6 then
            if a.val < 5 then
              0
            else
              0
          else
            if a.val < 7 then
              0
            else
              if a.val < 8 then
                0
              else
                0
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              0
            else
              0
          else
            if a.val < 12 then
              0
            else
              0
        else
          if a.val < 15 then
            if a.val < 14 then
              0
            else
              0
          else
            if a.val < 16 then
              0
            else
              if a.val < 17 then
                0
              else
                0
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            if a.val < 19 then
              0
            else
              0
          else
            if a.val < 21 then
              0
            else
              0
        else
          if a.val < 24 then
            if a.val < 23 then
              0
            else
              0
          else
            if a.val < 25 then
              0
            else
              if a.val < 26 then
                0
              else
                0
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              0
            else
              0
          else
            if a.val < 30 then
              0
            else
              0
        else
          if a.val < 33 then
            if a.val < 32 then
              0
            else
              0
          else
            if a.val < 34 then
              0
            else
              if a.val < 35 then
                0
              else
                0
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          if a.val < 38 then
            if a.val < 37 then
              0
            else
              0
          else
            if a.val < 39 then
              0
            else
              0
        else
          if a.val < 42 then
            if a.val < 41 then
              0
            else
              0
          else
            if a.val < 43 then
              0
            else
              if a.val < 44 then
                0
              else
                0
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              0
            else
              0
          else
            if a.val < 48 then
              0
            else
              0
        else
          if a.val < 51 then
            if a.val < 50 then
              0
            else
              0
          else
            if a.val < 52 then
              0
            else
              if a.val < 53 then
                0
              else
                0
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            if a.val < 55 then
              0
            else
              0
          else
            if a.val < 57 then
              0
            else
              0
        else
          if a.val < 60 then
            if a.val < 59 then
              0
            else
              0
          else
            if a.val < 61 then
              0
            else
              if a.val < 62 then
                0
              else
                0
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              0
            else
              0
          else
            if a.val < 66 then
              0
            else
              0
        else
          if a.val < 69 then
            if a.val < 68 then
              0
            else
              0
          else
            if a.val < 70 then
              0
            else
              if a.val < 71 then
                0
              else
                0
def flip2_0 (a : Fin 72) : Fin 72 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              10
            else
              11
          else
            if a.val < 3 then
              8
            else
              9
        else
          if a.val < 6 then
            if a.val < 5 then
              6
            else
              7
          else
            if a.val < 7 then
              4
            else
              if a.val < 8 then
                5
              else
                2
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              3
            else
              0
          else
            if a.val < 12 then
              1
            else
              58
        else
          if a.val < 15 then
            if a.val < 14 then
              59
            else
              56
          else
            if a.val < 16 then
              57
            else
              if a.val < 17 then
                54
              else
                55
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            if a.val < 19 then
              52
            else
              53
          else
            if a.val < 21 then
              50
            else
              51
        else
          if a.val < 24 then
            if a.val < 23 then
              48
            else
              49
          else
            if a.val < 25 then
              46
            else
              if a.val < 26 then
                47
              else
                44
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              45
            else
              42
          else
            if a.val < 30 then
              43
            else
              40
        else
          if a.val < 33 then
            if a.val < 32 then
              41
            else
              38
          else
            if a.val < 34 then
              39
            else
              if a.val < 35 then
                36
              else
                37
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          if a.val < 38 then
            if a.val < 37 then
              34
            else
              35
          else
            if a.val < 39 then
              32
            else
              33
        else
          if a.val < 42 then
            if a.val < 41 then
              30
            else
              31
          else
            if a.val < 43 then
              28
            else
              if a.val < 44 then
                29
              else
                26
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              27
            else
              24
          else
            if a.val < 48 then
              25
            else
              22
        else
          if a.val < 51 then
            if a.val < 50 then
              23
            else
              20
          else
            if a.val < 52 then
              21
            else
              if a.val < 53 then
                18
              else
                19
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            if a.val < 55 then
              16
            else
              17
          else
            if a.val < 57 then
              14
            else
              15
        else
          if a.val < 60 then
            if a.val < 59 then
              12
            else
              13
          else
            if a.val < 61 then
              60
            else
              if a.val < 62 then
                61
              else
                62
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              63
            else
              64
          else
            if a.val < 66 then
              65
            else
              66
        else
          if a.val < 69 then
            if a.val < 68 then
              67
            else
              68
          else
            if a.val < 70 then
              69
            else
              if a.val < 71 then
                70
              else
                71
def phase2_0 (a : Fin 72) : Fin 4 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              2
            else
              2
          else
            if a.val < 3 then
              2
            else
              2
        else
          if a.val < 6 then
            if a.val < 5 then
              2
            else
              2
          else
            if a.val < 7 then
              2
            else
              if a.val < 8 then
                2
              else
                2
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              2
            else
              2
          else
            if a.val < 12 then
              2
            else
              2
        else
          if a.val < 15 then
            if a.val < 14 then
              2
            else
              2
          else
            if a.val < 16 then
              2
            else
              if a.val < 17 then
                2
              else
                2
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            if a.val < 19 then
              2
            else
              2
          else
            if a.val < 21 then
              2
            else
              2
        else
          if a.val < 24 then
            if a.val < 23 then
              2
            else
              2
          else
            if a.val < 25 then
              2
            else
              if a.val < 26 then
                2
              else
                2
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              2
            else
              2
          else
            if a.val < 30 then
              2
            else
              2
        else
          if a.val < 33 then
            if a.val < 32 then
              2
            else
              2
          else
            if a.val < 34 then
              2
            else
              if a.val < 35 then
                2
              else
                2
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          if a.val < 38 then
            if a.val < 37 then
              2
            else
              2
          else
            if a.val < 39 then
              2
            else
              2
        else
          if a.val < 42 then
            if a.val < 41 then
              2
            else
              2
          else
            if a.val < 43 then
              2
            else
              if a.val < 44 then
                2
              else
                2
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              2
            else
              2
          else
            if a.val < 48 then
              2
            else
              2
        else
          if a.val < 51 then
            if a.val < 50 then
              2
            else
              2
          else
            if a.val < 52 then
              2
            else
              if a.val < 53 then
                2
              else
                2
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            if a.val < 55 then
              2
            else
              2
          else
            if a.val < 57 then
              2
            else
              2
        else
          if a.val < 60 then
            if a.val < 59 then
              2
            else
              2
          else
            if a.val < 61 then
              0
            else
              if a.val < 62 then
                0
              else
                0
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              0
            else
              0
          else
            if a.val < 66 then
              0
            else
              0
        else
          if a.val < 69 then
            if a.val < 68 then
              0
            else
              0
          else
            if a.val < 70 then
              0
            else
              if a.val < 71 then
                0
              else
                0
def flip2_1 (a : Fin 72) : Fin 72 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              10
            else
              11
          else
            if a.val < 3 then
              2
            else
              3
        else
          if a.val < 6 then
            if a.val < 5 then
              4
            else
              5
          else
            if a.val < 7 then
              6
            else
              if a.val < 8 then
                7
              else
                8
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              9
            else
              0
          else
            if a.val < 12 then
              1
            else
              44
        else
          if a.val < 15 then
            if a.val < 14 then
              45
            else
              46
          else
            if a.val < 16 then
              47
            else
              if a.val < 17 then
                48
              else
                49
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            if a.val < 19 then
              50
            else
              51
          else
            if a.val < 21 then
              52
            else
              53
        else
          if a.val < 24 then
            if a.val < 23 then
              54
            else
              55
          else
            if a.val < 25 then
              56
            else
              if a.val < 26 then
                57
              else
                58
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              59
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
                12
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              13
            else
              14
          else
            if a.val < 48 then
              15
            else
              16
        else
          if a.val < 51 then
            if a.val < 50 then
              17
            else
              18
          else
            if a.val < 52 then
              19
            else
              if a.val < 53 then
                20
              else
                21
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            if a.val < 55 then
              22
            else
              23
          else
            if a.val < 57 then
              24
            else
              25
        else
          if a.val < 60 then
            if a.val < 59 then
              26
            else
              27
          else
            if a.val < 61 then
              66
            else
              if a.val < 62 then
                67
              else
                64
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              65
            else
              62
          else
            if a.val < 66 then
              63
            else
              60
        else
          if a.val < 69 then
            if a.val < 68 then
              61
            else
              68
          else
            if a.val < 70 then
              69
            else
              if a.val < 71 then
                70
              else
                71
def phase2_1 (a : Fin 72) : Fin 4 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              0
            else
              0
          else
            if a.val < 3 then
              0
            else
              0
        else
          if a.val < 6 then
            if a.val < 5 then
              0
            else
              0
          else
            if a.val < 7 then
              0
            else
              if a.val < 8 then
                0
              else
                0
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              0
            else
              0
          else
            if a.val < 12 then
              0
            else
              0
        else
          if a.val < 15 then
            if a.val < 14 then
              0
            else
              0
          else
            if a.val < 16 then
              0
            else
              if a.val < 17 then
                0
              else
                0
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            if a.val < 19 then
              0
            else
              0
          else
            if a.val < 21 then
              0
            else
              0
        else
          if a.val < 24 then
            if a.val < 23 then
              0
            else
              0
          else
            if a.val < 25 then
              0
            else
              if a.val < 26 then
                0
              else
                0
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              0
            else
              0
          else
            if a.val < 30 then
              0
            else
              0
        else
          if a.val < 33 then
            if a.val < 32 then
              0
            else
              0
          else
            if a.val < 34 then
              0
            else
              if a.val < 35 then
                0
              else
                0
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          if a.val < 38 then
            if a.val < 37 then
              0
            else
              0
          else
            if a.val < 39 then
              0
            else
              0
        else
          if a.val < 42 then
            if a.val < 41 then
              0
            else
              0
          else
            if a.val < 43 then
              0
            else
              if a.val < 44 then
                0
              else
                0
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              0
            else
              0
          else
            if a.val < 48 then
              0
            else
              0
        else
          if a.val < 51 then
            if a.val < 50 then
              0
            else
              0
          else
            if a.val < 52 then
              0
            else
              if a.val < 53 then
                0
              else
                0
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            if a.val < 55 then
              0
            else
              0
          else
            if a.val < 57 then
              0
            else
              0
        else
          if a.val < 60 then
            if a.val < 59 then
              0
            else
              0
          else
            if a.val < 61 then
              2
            else
              if a.val < 62 then
                2
              else
                2
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              2
            else
              2
          else
            if a.val < 66 then
              2
            else
              2
        else
          if a.val < 69 then
            if a.val < 68 then
              2
            else
              0
          else
            if a.val < 70 then
              0
            else
              if a.val < 71 then
                0
              else
                0
def flip2_2 (a : Fin 72) : Fin 72 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              0
            else
              1
          else
            if a.val < 3 then
              8
            else
              9
        else
          if a.val < 6 then
            if a.val < 5 then
              4
            else
              5
          else
            if a.val < 7 then
              6
            else
              if a.val < 8 then
                7
              else
                2
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              3
            else
              10
          else
            if a.val < 12 then
              11
            else
              24
        else
          if a.val < 15 then
            if a.val < 14 then
              25
            else
              26
          else
            if a.val < 16 then
              27
            else
              if a.val < 17 then
                20
              else
                21
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            if a.val < 19 then
              22
            else
              23
          else
            if a.val < 21 then
              16
            else
              17
        else
          if a.val < 24 then
            if a.val < 23 then
              18
            else
              19
          else
            if a.val < 25 then
              12
            else
              if a.val < 26 then
                13
              else
                14
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              15
            else
              32
          else
            if a.val < 30 then
              33
            else
              34
        else
          if a.val < 33 then
            if a.val < 32 then
              35
            else
              28
          else
            if a.val < 34 then
              29
            else
              if a.val < 35 then
                30
              else
                31
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          if a.val < 38 then
            if a.val < 37 then
              40
            else
              41
          else
            if a.val < 39 then
              42
            else
              43
        else
          if a.val < 42 then
            if a.val < 41 then
              36
            else
              37
          else
            if a.val < 43 then
              38
            else
              if a.val < 44 then
                39
              else
                56
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              57
            else
              58
          else
            if a.val < 48 then
              59
            else
              52
        else
          if a.val < 51 then
            if a.val < 50 then
              53
            else
              54
          else
            if a.val < 52 then
              55
            else
              if a.val < 53 then
                48
              else
                49
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            if a.val < 55 then
              50
            else
              51
          else
            if a.val < 57 then
              44
            else
              45
        else
          if a.val < 60 then
            if a.val < 59 then
              46
            else
              47
          else
            if a.val < 61 then
              66
            else
              if a.val < 62 then
                67
              else
                62
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              63
            else
              64
          else
            if a.val < 66 then
              65
            else
              60
        else
          if a.val < 69 then
            if a.val < 68 then
              61
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
def phase2_2 (a : Fin 72) : Fin 4 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              0
            else
              0
          else
            if a.val < 3 then
              0
            else
              0
        else
          if a.val < 6 then
            if a.val < 5 then
              0
            else
              0
          else
            if a.val < 7 then
              0
            else
              if a.val < 8 then
                0
              else
                0
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              0
            else
              0
          else
            if a.val < 12 then
              0
            else
              0
        else
          if a.val < 15 then
            if a.val < 14 then
              0
            else
              0
          else
            if a.val < 16 then
              0
            else
              if a.val < 17 then
                0
              else
                0
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            if a.val < 19 then
              0
            else
              0
          else
            if a.val < 21 then
              0
            else
              0
        else
          if a.val < 24 then
            if a.val < 23 then
              0
            else
              0
          else
            if a.val < 25 then
              0
            else
              if a.val < 26 then
                0
              else
                0
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              0
            else
              0
          else
            if a.val < 30 then
              0
            else
              0
        else
          if a.val < 33 then
            if a.val < 32 then
              0
            else
              0
          else
            if a.val < 34 then
              0
            else
              if a.val < 35 then
                0
              else
                0
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          if a.val < 38 then
            if a.val < 37 then
              0
            else
              0
          else
            if a.val < 39 then
              0
            else
              0
        else
          if a.val < 42 then
            if a.val < 41 then
              0
            else
              0
          else
            if a.val < 43 then
              0
            else
              if a.val < 44 then
                0
              else
                0
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              0
            else
              0
          else
            if a.val < 48 then
              0
            else
              0
        else
          if a.val < 51 then
            if a.val < 50 then
              0
            else
              0
          else
            if a.val < 52 then
              0
            else
              if a.val < 53 then
                0
              else
                0
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            if a.val < 55 then
              0
            else
              0
          else
            if a.val < 57 then
              0
            else
              0
        else
          if a.val < 60 then
            if a.val < 59 then
              0
            else
              0
          else
            if a.val < 61 then
              0
            else
              if a.val < 62 then
                0
              else
                0
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              0
            else
              0
          else
            if a.val < 66 then
              0
            else
              0
        else
          if a.val < 69 then
            if a.val < 68 then
              0
            else
              2
          else
            if a.val < 70 then
              2
            else
              if a.val < 71 then
                2
              else
                2
def flip2_3 (a : Fin 72) : Fin 72 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              0
            else
              1
          else
            if a.val < 3 then
              2
            else
              3
        else
          if a.val < 6 then
            if a.val < 5 then
              6
            else
              7
          else
            if a.val < 7 then
              4
            else
              if a.val < 8 then
                5
              else
                8
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              9
            else
              10
          else
            if a.val < 12 then
              11
            else
              14
        else
          if a.val < 15 then
            if a.val < 14 then
              15
            else
              12
          else
            if a.val < 16 then
              13
            else
              if a.val < 17 then
                18
              else
                19
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            if a.val < 19 then
              16
            else
              17
          else
            if a.val < 21 then
              22
            else
              23
        else
          if a.val < 24 then
            if a.val < 23 then
              20
            else
              21
          else
            if a.val < 25 then
              26
            else
              if a.val < 26 then
                27
              else
                24
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              25
            else
              30
          else
            if a.val < 30 then
              31
            else
              28
        else
          if a.val < 33 then
            if a.val < 32 then
              29
            else
              34
          else
            if a.val < 34 then
              35
            else
              if a.val < 35 then
                32
              else
                33
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          if a.val < 38 then
            if a.val < 37 then
              38
            else
              39
          else
            if a.val < 39 then
              36
            else
              37
        else
          if a.val < 42 then
            if a.val < 41 then
              42
            else
              43
          else
            if a.val < 43 then
              40
            else
              if a.val < 44 then
                41
              else
                46
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              47
            else
              44
          else
            if a.val < 48 then
              45
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
              58
            else
              59
        else
          if a.val < 60 then
            if a.val < 59 then
              56
            else
              57
          else
            if a.val < 61 then
              60
            else
              if a.val < 62 then
                61
              else
                64
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              65
            else
              62
          else
            if a.val < 66 then
              63
            else
              66
        else
          if a.val < 69 then
            if a.val < 68 then
              67
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
def phase2_3 (a : Fin 72) : Fin 4 :=
  if a.val < 36 then
    if a.val < 18 then
      if a.val < 9 then
        if a.val < 4 then
          if a.val < 2 then
            if a.val < 1 then
              0
            else
              0
          else
            if a.val < 3 then
              0
            else
              0
        else
          if a.val < 6 then
            if a.val < 5 then
              0
            else
              0
          else
            if a.val < 7 then
              0
            else
              if a.val < 8 then
                0
              else
                0
      else
        if a.val < 13 then
          if a.val < 11 then
            if a.val < 10 then
              0
            else
              0
          else
            if a.val < 12 then
              0
            else
              0
        else
          if a.val < 15 then
            if a.val < 14 then
              0
            else
              0
          else
            if a.val < 16 then
              0
            else
              if a.val < 17 then
                0
              else
                0
    else
      if a.val < 27 then
        if a.val < 22 then
          if a.val < 20 then
            if a.val < 19 then
              0
            else
              0
          else
            if a.val < 21 then
              0
            else
              0
        else
          if a.val < 24 then
            if a.val < 23 then
              0
            else
              0
          else
            if a.val < 25 then
              0
            else
              if a.val < 26 then
                0
              else
                0
      else
        if a.val < 31 then
          if a.val < 29 then
            if a.val < 28 then
              0
            else
              0
          else
            if a.val < 30 then
              0
            else
              0
        else
          if a.val < 33 then
            if a.val < 32 then
              0
            else
              0
          else
            if a.val < 34 then
              0
            else
              if a.val < 35 then
                0
              else
                0
  else
    if a.val < 54 then
      if a.val < 45 then
        if a.val < 40 then
          if a.val < 38 then
            if a.val < 37 then
              0
            else
              0
          else
            if a.val < 39 then
              0
            else
              0
        else
          if a.val < 42 then
            if a.val < 41 then
              0
            else
              0
          else
            if a.val < 43 then
              0
            else
              if a.val < 44 then
                0
              else
                0
      else
        if a.val < 49 then
          if a.val < 47 then
            if a.val < 46 then
              0
            else
              0
          else
            if a.val < 48 then
              0
            else
              0
        else
          if a.val < 51 then
            if a.val < 50 then
              0
            else
              0
          else
            if a.val < 52 then
              0
            else
              if a.val < 53 then
                0
              else
                0
    else
      if a.val < 63 then
        if a.val < 58 then
          if a.val < 56 then
            if a.val < 55 then
              0
            else
              0
          else
            if a.val < 57 then
              0
            else
              0
        else
          if a.val < 60 then
            if a.val < 59 then
              0
            else
              0
          else
            if a.val < 61 then
              0
            else
              if a.val < 62 then
                0
              else
                0
      else
        if a.val < 67 then
          if a.val < 65 then
            if a.val < 64 then
              0
            else
              0
          else
            if a.val < 66 then
              0
            else
              0
        else
          if a.val < 69 then
            if a.val < 68 then
              0
            else
              0
          else
            if a.val < 70 then
              0
            else
              if a.val < 71 then
                0
              else
                0

def flipIndex (r : Fin 3) (i : Fin 4) : Fin (count r) → Fin (count r) := match r with
  | 0 => ![flip0_0,flip0_1,flip0_2,flip0_3] i
  | 1 => ![flip1_0,flip1_1,flip1_2,flip1_3] i
  | 2 => ![flip2_0,flip2_1,flip2_2,flip2_3] i

def phaseIndex (r : Fin 3) (i : Fin 4) : Fin (count r) → Fin 4 := match r with
  | 0 => ![phase0_0,phase0_1,phase0_2,phase0_3] i
  | 1 => ![phase1_0,phase1_1,phase1_2,phase1_3] i
  | 2 => ![phase2_0,phase2_1,phase2_2,phase2_3] i

def root : Fin 4 → GaussianInt := ![1,⟨0,1⟩,-1,⟨0,-1⟩]
def flipPhase (r : Fin 3) (i : Fin 4) (a : Fin (count r)) := root (phaseIndex r i a)
def sign (i j : Fin 4) : GaussianInt := if i = j then -1 else 1
theorem phase_four (r : Fin 3) (i : Fin 4) (a : Fin (count r)) : (flipPhase r i a)^4 = 1 := by
  have hr : ∀ p : Fin 4, (root p)^4 = 1 := by decide +kernel
  exact hr _
end Math.HiggsFourWaveCubature
