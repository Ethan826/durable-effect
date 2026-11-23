export const nine = (a: number, b: string | undefined): string => {
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
  const c = a > 0 && a < 9 && a !== 5
  const d = b ?? "none"
  return String(c || d === "x")
}
