dtc v1.5.0

```shell
wget "https://github.com/dgibson/dtc/archive/v1.5.0.tar.gz"
sha256sum -c <<EOF
3416f10ca69b0b911f027a9cb96471485dd8705705fc4813283f963299eaae0a  v1.5.0.tar.gz
EOF
tar xzf v1.5.0.tar.gz
cd dtc-1.5.0/
patch -p1 <<EOF
--- a/Makefile	2019-08-21 14:02:41.492913319 +0100
+++ b/Makefile	2019-08-21 14:01:34.765765921 +0100
@@ -18,7 +18,7 @@
 CPPFLAGS = -I libfdt -I .
 WARNINGS = -Wall -Wpointer-arith -Wcast-qual -Wnested-externs \\
 	-Wstrict-prototypes -Wmissing-prototypes -Wredundant-decls -Wshadow
-CFLAGS = -g -Os \$(SHAREDLIB_CFLAGS) -Werror \$(WARNINGS)
+CFLAGS = -g -Os \$(SHAREDLIB_CFLAGS) -Werror \$(WARNINGS) -static

 BISON = bison
 LEX = flex
EOF
make
strip dtc fdtoverlay
```

