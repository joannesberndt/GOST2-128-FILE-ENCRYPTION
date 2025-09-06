# GOST2-128-FILE-ENCRYPTION

# File encryption with GOST2-128 in CBC and GCM mode (Go language)

* Build:
*   go build -o gost2file gost2-128-cbc.go

* Usage:
*   ./gost2file c <input_file>   -> produces <input_file>.gost2
*   ./gost2file d <input_file>   -> removes .gost2 suffix if present, else appends .dec

* Build:
*   go build -o gost2gcm gost2-128-gcm.go
*
* Usage:
*   ./gost2gcm c <input_file>   -> produces <input_file>.gost2
*   ./gost2gcm d <input_file>   -> removes .gost2 suffix if present, else appends .dec
