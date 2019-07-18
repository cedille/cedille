const cedilleArchive = JSON.parse(document.getElementById('spans').innerHTML);
const cedilleData = document.getElementById('cedille-data');
const cedilleCode = document.getElementById('cedille-code-block');
const cedilleFiles = document.getElementById('cedille-files');
const emptyNode = document.createTextNode("");

const removeClassFromSpans = (className, htmlSpans) => {
  htmlSpans.forEach(htmlSpan => htmlSpan.classList.remove(className));
};

const spanLength = ({ start, end }) => {
  return Math.abs(end - start);
};

const isArray = x => {
  return x && typeof x === 'object' && x.length !== null;
};

const addEventListeners = (span, htmlSpan, htmlSpans) => {
  htmlSpan.addEventListener('click', event => {
    event.stopPropagation();
    removeClassFromSpans('highlight', htmlSpans);
    htmlSpan.classList.add('highlight');
    displayData(span);
  });

  htmlSpan.addEventListener('mouseover', event => {
    event.stopPropagation();
    removeClassFromSpans('hover-highlight', htmlSpans);
    htmlSpan.classList.add('hover-highlight');
  });

  htmlSpan.addEventListener('mouseout', () => {
    htmlSpan.classList.remove('hover-highlight');
  });
};

const createDiv = (className, text, children) => {
  const node = document.createElement('div');
  node.className = className;

  if (isArray(text)) {
    node.innerText = text[1];
  } else if (text) {
    node.innerText = text;
  }

  if (children) {
    children.forEach(child => node.appendChild(child));
  }

  return node;
};

const displayData = ({name, start, end, data}) => {
  const displayData = {
    name,
    start,
    end,
    ...data
  };

  clearData();
  Object.keys(displayData).forEach((key) => {
    const keyDiv = createDiv('cedille-key', key)
    const valueDiv = createDiv('cedille-value', displayData[key]);
    const bodyDiv = createDiv('cedille-pair', null, [keyDiv, valueDiv]);
    cedilleData.appendChild(bodyDiv);
  });
};

const clearData = () => {
  cedilleData.innerHTML = null;
};

const displayCode = (filename) => {
  const source = cedilleArchive.files[filename].source;
  const spans = cedilleArchive.files[filename].spans.spans.map(([name, start, end, data]) => {
    return { name, start, end, data };
  });
  const nodes = [null, ...source].map(c => document.createTextNode(c));
  const spansByAscendingLength = spans.sort((a, b) => spanLength(a) - spanLength(b));
  const htmlSpans = [];

  spansByAscendingLength.forEach(span => {
    const htmlSpan = document.createElement("span");
    htmlSpan.className = 'cedille-span';
    htmlSpans.push(htmlSpan);
    addEventListeners(span, htmlSpan, htmlSpans);

    for(let i = span.start; i < span.end; i++) {
      htmlSpan.appendChild(nodes[i] || emptyNode);
      nodes[i] = (i === span.start) ? htmlSpan : null;
    }
  });

  cedilleCode.innerHTML = null;
  cedilleCode.appendChild(nodes[1]);
};

const createFileLinks = () => {
  const filenames = Object.keys(cedilleArchive.files).sort();

  filenames.forEach(filename => {
    const fileNode = createDiv('cedille-file', filename);

    fileNode.addEventListener('click', () => {
      if (fileNode.classList.contains('active')) return;
      removeClassFromSpans('active', [...cedilleFiles.children]);
      fileNode.classList.add('active');
      clearData();
      displayCode(filename);
    });

    if (filename === cedilleArchive.archiveFilename) {
      fileNode.classList.add('active');
    }

    cedilleFiles.append(fileNode);
  });
};

createFileLinks();
displayCode(cedilleArchive.archiveFilename);
