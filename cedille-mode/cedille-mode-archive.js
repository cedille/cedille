
const cedilleSpans = JSON.parse(document.getElementById('spans').innerHTML);
const htmlSpans = [...document.getElementsByClassName('cedille-span')];

function removeClassFromSpans(className) {
  htmlSpans.forEach(htmlSpan => htmlSpan.classList.remove(className));
}

htmlSpans.forEach(htmlSpan => {
  htmlSpan.addEventListener('click', () => {
    removeClassFromSpans('highlight');
    htmlSpan.classList.add('highlight');
  }, { capture: true });

  htmlSpan.addEventListener('mouseover', () => {
    removeClassFromSpans('hover-highlight');
    htmlSpan.classList.add('hover-highlight');
  }, { capture: true });

  htmlSpan.addEventListener('mouseout', () => {
    htmlSpan.classList.remove('hover-highlight');
  });
});
