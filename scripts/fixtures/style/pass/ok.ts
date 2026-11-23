export const depthThree = (a: boolean, b: boolean, c: boolean): number => {
  if (a) {
    if (b) {
      if (c) {
        return 1
      }
    }
  }
  return 0
}

export const eight = (a: number, b: string | undefined): string => {
  try {
    if (a > 1) return "if"
    switch (a) {
      case 1:
        return "one"
      case 2:
        return "two"
      default:
        break
    }
  } catch {
    return a > 0 ? "pos" : "neg"
  }
  const c = a > 0 && a < 9
  const d = b ?? "none"
  return String(c || d === "x")
}

export const eightBindings = (a: number, b: number): number => {
  const c = 1
  const d = 2
  const e = 3
  const f = 4
  const g = 5
  const h = 6
  return a + b + c + d + e + f + g + h
}

export const thirty = (): void => {
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
  Math.abs(1)
}

export const generator = function* () {
  yield 1
}

export const note = "// eslint-disable-next-line and @ts-ignore"
export const block = `/* @ts-nocheck */`
export const wide = "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx"
