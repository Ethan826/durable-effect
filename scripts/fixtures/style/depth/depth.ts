export const deep = (a: boolean, b: boolean, c: boolean, d: boolean) => {
  if (a) {
    if (b) {
      if (c) {
        if (d) {
          return 1
        }
      }
    }
  }
  return 0
}
