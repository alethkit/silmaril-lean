module ServiceCycle {
  var phase: int

  val atStart = phase == 0
  action init = phase' = 0
  action service = all { phase == 1, phase' = 3 }
  action step = any {
    all { phase == 0, phase' = 1 },
    all { phase == 1, phase' = 2 },
    all { phase == 2 or phase == 3, phase' = 1 },
    service,
  }

  temporal safe = atStart and always(step.orKeep(phase))
  temporal weak = safe and weakFair(service, phase)
  temporal strong = safe and strongFair(service, phase)
}
