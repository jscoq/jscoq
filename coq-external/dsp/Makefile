all: dspsupport.vo

dspsupport.vo: dspsupport.v
	coqc -R . Dsp dspsupport.v

clean:
	rm -f dspsupport.{aux,vio,vo,glob}
