This is an old and likely stale TODO, kept for reference as some items
may be useful:

 - [ ] Automatic parsing mode.
 - [ ] Execution gutters.
 - [ ] Support for UI layouts.
 - [ ] Dark theme - color scheme and icon set
 - [ ] Printer-friendly formatting in documents.
 - [ ] Further fine-tuning of auto-completion

Notes and quirks about the STM / protocol:

+ Possible race: we cancel, then we add before the cancelled event
  arrives.

+ Be careful about re-execing states, as this may brind back the
  parser to an improper state [EJGA I think I fixed this in Coq
  upstream but we should double-check]

+ For some commands the STM is buggy, and won't respect `newtip`
