CC=coqc
CFLAGS=

all: SystemFC SystemFProp

SystemFProp: SystemFProp.v SystemFC
	$(CC) $(CFLAGS) SystemFProp.v

SystemFC: SystemFC.v SfLib
	$(CC) $(CFLAGS) SystemFC.v

SfLib: SfLib.v
	$(CC) $(CFLAGS) SfLib.v

clean:
	rm *.vo *.glob
